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
% DateTime   : Thu Dec  3 13:02:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  227 ( 493 expanded)
%              Number of leaves         :   44 ( 210 expanded)
%              Depth                    :   20
%              Number of atoms          : 1158 (2726 expanded)
%              Number of equality atoms :  245 ( 739 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (30918)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f530,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f155,f163,f168,f191,f214,f221,f235,f253,f294,f304,f368,f396,f416,f466,f517,f529])).

fof(f529,plain,
    ( spl4_28
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f528,f374,f146,f141,f136,f131,f126,f121,f116,f101,f315])).

fof(f315,plain,
    ( spl4_28
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f101,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f116,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f121,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f126,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f131,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f136,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f141,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f146,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f374,plain,
    ( spl4_33
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f528,plain,
    ( v2_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f527,f69])).

fof(f69,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f527,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f526,f376])).

fof(f376,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f374])).

fof(f526,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f525,f133])).

fof(f133,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f131])).

fof(f525,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f524,f128])).

fof(f128,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f524,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f342,f103])).

fof(f103,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f342,plain,
    ( v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(resolution,[],[f339,f123])).

fof(f123,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f339,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | v2_funct_1(X1)
        | k1_xboole_0 = X0
        | ~ v2_funct_1(k5_relat_1(sK2,X1))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f338,f148])).

fof(f148,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f338,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k5_relat_1(sK2,X1))
        | v2_funct_1(X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f337,f138])).

fof(f138,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f337,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k5_relat_1(sK2,X1))
        | v2_funct_1(X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(duplicate_literal_removal,[],[f336])).

fof(f336,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k5_relat_1(sK2,X1))
        | v2_funct_1(X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(superposition,[],[f330,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f330,plain,
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
    inference(subsumption_resolution,[],[f329,f148])).

fof(f329,plain,
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
    inference(subsumption_resolution,[],[f328,f143])).

fof(f143,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f141])).

fof(f328,plain,
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
    inference(subsumption_resolution,[],[f327,f138])).

fof(f327,plain,
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
    inference(trivial_inequality_removal,[],[f322])).

fof(f322,plain,
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
    inference(superposition,[],[f60,f118])).

fof(f118,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f517,plain,
    ( ~ spl4_28
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_24
    | ~ spl4_27
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f516,f463,f299,f248,f230,f186,f165,f160,f146,f131,f106,f91,f315])).

fof(f91,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f106,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f160,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f165,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f186,plain,
    ( spl4_18
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f230,plain,
    ( spl4_23
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f248,plain,
    ( spl4_24
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f299,plain,
    ( spl4_27
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f463,plain,
    ( spl4_35
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f516,plain,
    ( ~ v2_funct_1(sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_24
    | ~ spl4_27
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f515,f250])).

fof(f250,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f248])).

fof(f515,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_27
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f514,f301])).

fof(f301,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f299])).

fof(f514,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_35 ),
    inference(trivial_inequality_removal,[],[f513])).

fof(f513,plain,
    ( k6_relat_1(sK1) != k6_relat_1(sK1)
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f512,f232])).

fof(f232,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f230])).

fof(f512,plain,
    ( k6_relat_1(k1_relat_1(sK3)) != k6_relat_1(sK1)
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f485,f188])).

fof(f188,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f186])).

fof(f485,plain,
    ( k6_relat_1(k1_relat_1(sK3)) != k6_relat_1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f484,f167])).

fof(f167,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f165])).

fof(f484,plain,
    ( k6_relat_1(k1_relat_1(sK3)) != k6_relat_1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f483,f148])).

fof(f483,plain,
    ( k6_relat_1(k1_relat_1(sK3)) != k6_relat_1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f482,f162])).

fof(f162,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f160])).

fof(f482,plain,
    ( k6_relat_1(k1_relat_1(sK3)) != k6_relat_1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f481,f133])).

fof(f481,plain,
    ( k6_relat_1(k1_relat_1(sK3)) != k6_relat_1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f480,f108])).

% (30918)Refutation not found, incomplete strategy% (30918)------------------------------
% (30918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30918)Termination reason: Refutation not found, incomplete strategy

% (30918)Memory used [KB]: 10746
% (30918)Time elapsed: 0.138 s
% (30918)------------------------------
% (30918)------------------------------
fof(f108,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f480,plain,
    ( k6_relat_1(k1_relat_1(sK3)) != k6_relat_1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | spl4_1
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f477,f93])).

fof(f93,plain,
    ( k2_funct_1(sK2) != sK3
    | spl4_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f477,plain,
    ( k6_relat_1(k1_relat_1(sK3)) != k6_relat_1(k2_relat_1(sK2))
    | k2_funct_1(sK2) = sK3
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ spl4_35 ),
    inference(superposition,[],[f241,f465])).

fof(f465,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f463])).

fof(f241,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) != k6_relat_1(k2_relat_1(k2_funct_1(X0)))
      | k2_funct_1(k2_funct_1(X0)) = X0
      | k2_relat_1(X0) != k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f239])).

fof(f239,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) != k6_relat_1(k2_relat_1(k2_funct_1(X0)))
      | k2_funct_1(k2_funct_1(X0)) = X0
      | k2_relat_1(X0) != k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f55,f56])).

fof(f56,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_funct_1(X0) = X1
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
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
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f466,plain,
    ( spl4_35
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_27
    | ~ spl4_28
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f461,f374,f315,f299,f230,f186,f165,f160,f146,f131,f463])).

fof(f461,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_27
    | ~ spl4_28
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f460,f188])).

fof(f460,plain,
    ( sK1 != k2_relat_1(sK2)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_23
    | ~ spl4_27
    | ~ spl4_28
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f459,f232])).

fof(f459,plain,
    ( sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_27
    | ~ spl4_28
    | ~ spl4_33 ),
    inference(trivial_inequality_removal,[],[f458])).

fof(f458,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_27
    | ~ spl4_28
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f457,f301])).

fof(f457,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_28
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f456,f162])).

fof(f456,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_28
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f455,f133])).

fof(f455,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_28
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f454,f167])).

fof(f454,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_28
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f453,f148])).

fof(f453,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_28
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f450,f317])).

fof(f317,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f315])).

fof(f450,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_33 ),
    inference(superposition,[],[f55,f376])).

fof(f416,plain,
    ( spl4_33
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f415,f365,f146,f136,f131,f121,f374])).

fof(f365,plain,
    ( spl4_31
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f415,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f414,f148])).

fof(f414,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f413,f138])).

fof(f413,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f412,f133])).

fof(f412,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f404,f123])).

fof(f404,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_31 ),
    inference(superposition,[],[f76,f367])).

fof(f367,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f365])).

fof(f396,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_30 ),
    inference(avatar_contradiction_clause,[],[f395])).

fof(f395,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_30 ),
    inference(subsumption_resolution,[],[f394,f148])).

fof(f394,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | spl4_30 ),
    inference(subsumption_resolution,[],[f393,f138])).

fof(f393,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_30 ),
    inference(subsumption_resolution,[],[f392,f133])).

fof(f392,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | spl4_30 ),
    inference(subsumption_resolution,[],[f389,f123])).

fof(f389,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_30 ),
    inference(resolution,[],[f363,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f363,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_30 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl4_30
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f368,plain,
    ( ~ spl4_30
    | spl4_31
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f357,f152,f365,f361])).

fof(f152,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f357,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_13 ),
    inference(resolution,[],[f238,f154])).

fof(f154,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f152])).

fof(f238,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f70,f79])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f304,plain,
    ( spl4_27
    | ~ spl4_7
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f303,f291,f121,f299])).

fof(f291,plain,
    ( spl4_26
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f303,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f296,f123])).

fof(f296,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_26 ),
    inference(superposition,[],[f77,f293])).

fof(f293,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f291])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

% (30910)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% (30919)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (30912)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

% (30912)Refutation not found, incomplete strategy% (30912)------------------------------
% (30912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30912)Termination reason: Refutation not found, incomplete strategy

% (30912)Memory used [KB]: 11001
% (30912)Time elapsed: 0.143 s
% (30912)------------------------------
% (30912)------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f294,plain,
    ( spl4_26
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f289,f152,f146,f141,f136,f131,f126,f121,f291])).

fof(f289,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f288,f133])).

fof(f288,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f287,f128])).

fof(f287,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f286,f123])).

fof(f286,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f285,f148])).

fof(f285,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f284,f143])).

fof(f284,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f281,f138])).

fof(f281,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_13 ),
    inference(resolution,[],[f280,f154])).

fof(f280,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f72,f73])).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f253,plain,
    ( spl4_24
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f252,f218,f136,f248])).

fof(f218,plain,
    ( spl4_22
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f252,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f244,f138])).

fof(f244,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_22 ),
    inference(superposition,[],[f80,f220])).

fof(f220,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f218])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f235,plain,
    ( spl4_23
    | ~ spl4_7
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f234,f211,f121,f230])).

fof(f211,plain,
    ( spl4_21
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f234,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f226,f123])).

fof(f226,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_21 ),
    inference(superposition,[],[f80,f213])).

fof(f213,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f211])).

fof(f221,plain,
    ( spl4_22
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f216,f141,f136,f96,f218])).

fof(f96,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f216,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f215,f98])).

fof(f98,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f215,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f206,f143])).

fof(f206,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_10 ),
    inference(resolution,[],[f62,f138])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f214,plain,
    ( spl4_21
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f209,f126,f121,f101,f211])).

fof(f209,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f208,f103])).

fof(f208,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f205,f128])).

fof(f205,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f62,f123])).

fof(f191,plain,
    ( spl4_18
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f190,f136,f116,f186])).

fof(f190,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f183,f138])).

fof(f183,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(superposition,[],[f118,f77])).

fof(f168,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f157,f136,f165])).

fof(f157,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(resolution,[],[f78,f138])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f163,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f156,f121,f160])).

fof(f156,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f78,f123])).

fof(f155,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f150,f111,f152])).

fof(f111,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f150,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f113,f73])).

fof(f113,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f149,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f43,f146])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f39,f38])).

fof(f38,plain,
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

fof(f39,plain,
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

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f144,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f44,f141])).

fof(f44,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f139,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f45,f136])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f134,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f46,f131])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f129,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f47,f126])).

fof(f47,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f124,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f48,f121])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f119,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f49,f116])).

fof(f49,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f114,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f50,f111])).

fof(f50,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f109,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f51,f106])).

fof(f51,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f104,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f52,f101])).

fof(f52,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f40])).

fof(f99,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f53,f96])).

fof(f53,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f94,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f54,f91])).

fof(f54,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (30930)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.51  % (30904)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (30908)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (30906)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (30915)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (30916)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (30923)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.51  % (30902)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (30905)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (30925)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (30911)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (30913)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (30907)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (30924)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (30917)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (30928)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.52  % (30923)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (30926)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (30929)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (30922)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (30909)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (30903)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (30931)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (30932)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (30921)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (30920)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (30914)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  % (30918)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  fof(f530,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f155,f163,f168,f191,f214,f221,f235,f253,f294,f304,f368,f396,f416,f466,f517,f529])).
% 0.20/0.54  fof(f529,plain,(
% 0.20/0.54    spl4_28 | spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_33),
% 0.20/0.54    inference(avatar_split_clause,[],[f528,f374,f146,f141,f136,f131,f126,f121,f116,f101,f315])).
% 0.20/0.54  fof(f315,plain,(
% 0.20/0.54    spl4_28 <=> v2_funct_1(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.54  fof(f101,plain,(
% 0.20/0.54    spl4_3 <=> k1_xboole_0 = sK0),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.54  fof(f126,plain,(
% 0.20/0.54    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.54  fof(f131,plain,(
% 0.20/0.54    spl4_9 <=> v1_funct_1(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.54  fof(f136,plain,(
% 0.20/0.54    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.54  fof(f141,plain,(
% 0.20/0.54    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.54  fof(f146,plain,(
% 0.20/0.54    spl4_12 <=> v1_funct_1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.54  fof(f374,plain,(
% 0.20/0.54    spl4_33 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.20/0.54  fof(f528,plain,(
% 0.20/0.54    v2_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_33)),
% 0.20/0.54    inference(subsumption_resolution,[],[f527,f69])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.20/0.54  fof(f527,plain,(
% 0.20/0.54    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_33)),
% 0.20/0.54    inference(forward_demodulation,[],[f526,f376])).
% 0.20/0.54  fof(f376,plain,(
% 0.20/0.54    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_33),
% 0.20/0.54    inference(avatar_component_clause,[],[f374])).
% 0.20/0.54  fof(f526,plain,(
% 0.20/0.54    v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 0.20/0.54    inference(subsumption_resolution,[],[f525,f133])).
% 0.20/0.54  fof(f133,plain,(
% 0.20/0.54    v1_funct_1(sK3) | ~spl4_9),
% 0.20/0.54    inference(avatar_component_clause,[],[f131])).
% 0.20/0.54  fof(f525,plain,(
% 0.20/0.54    v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 0.20/0.54    inference(subsumption_resolution,[],[f524,f128])).
% 0.20/0.54  fof(f128,plain,(
% 0.20/0.54    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 0.20/0.54    inference(avatar_component_clause,[],[f126])).
% 0.20/0.54  fof(f524,plain,(
% 0.20/0.54    v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 0.20/0.54    inference(subsumption_resolution,[],[f342,f103])).
% 0.20/0.54  fof(f103,plain,(
% 0.20/0.54    k1_xboole_0 != sK0 | spl4_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f101])).
% 0.20/0.54  fof(f342,plain,(
% 0.20/0.54    v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 0.20/0.54    inference(resolution,[],[f339,f123])).
% 0.20/0.54  fof(f123,plain,(
% 0.20/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f121])).
% 0.20/0.54  fof(f339,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~v2_funct_1(k5_relat_1(sK2,X1)) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 0.20/0.54    inference(subsumption_resolution,[],[f338,f148])).
% 0.20/0.54  fof(f148,plain,(
% 0.20/0.54    v1_funct_1(sK2) | ~spl4_12),
% 0.20/0.54    inference(avatar_component_clause,[],[f146])).
% 0.20/0.54  fof(f338,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 0.20/0.54    inference(subsumption_resolution,[],[f337,f138])).
% 0.20/0.54  fof(f138,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 0.20/0.54    inference(avatar_component_clause,[],[f136])).
% 0.20/0.54  fof(f337,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f336])).
% 0.20/0.54  fof(f336,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 0.20/0.54    inference(superposition,[],[f330,f76])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.54    inference(flattening,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.20/0.54  fof(f330,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 0.20/0.54    inference(subsumption_resolution,[],[f329,f148])).
% 0.20/0.54  fof(f329,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11)),
% 0.20/0.54    inference(subsumption_resolution,[],[f328,f143])).
% 0.20/0.54  fof(f143,plain,(
% 0.20/0.54    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 0.20/0.54    inference(avatar_component_clause,[],[f141])).
% 0.20/0.54  fof(f328,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10)),
% 0.20/0.54    inference(subsumption_resolution,[],[f327,f138])).
% 0.20/0.54  fof(f327,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f322])).
% 0.20/0.54  fof(f322,plain,(
% 0.20/0.54    ( ! [X0,X1] : (sK1 != sK1 | k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 0.20/0.54    inference(superposition,[],[f60,f118])).
% 0.20/0.54  fof(f118,plain,(
% 0.20/0.54    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f116])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.54    inference(flattening,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.54    inference(ennf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 0.20/0.54  fof(f517,plain,(
% 0.20/0.54    ~spl4_28 | spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_23 | ~spl4_24 | ~spl4_27 | ~spl4_35),
% 0.20/0.54    inference(avatar_split_clause,[],[f516,f463,f299,f248,f230,f186,f165,f160,f146,f131,f106,f91,f315])).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.54  fof(f106,plain,(
% 0.20/0.54    spl4_4 <=> v2_funct_1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.54  fof(f160,plain,(
% 0.20/0.54    spl4_14 <=> v1_relat_1(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.54  fof(f165,plain,(
% 0.20/0.54    spl4_15 <=> v1_relat_1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.54  fof(f186,plain,(
% 0.20/0.54    spl4_18 <=> sK1 = k2_relat_1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.54  fof(f230,plain,(
% 0.20/0.54    spl4_23 <=> sK1 = k1_relat_1(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.54  fof(f248,plain,(
% 0.20/0.54    spl4_24 <=> sK0 = k1_relat_1(sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.54  fof(f299,plain,(
% 0.20/0.54    spl4_27 <=> sK0 = k2_relat_1(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.20/0.54  fof(f463,plain,(
% 0.20/0.54    spl4_35 <=> sK2 = k2_funct_1(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.20/0.54  fof(f516,plain,(
% 0.20/0.54    ~v2_funct_1(sK3) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_23 | ~spl4_24 | ~spl4_27 | ~spl4_35)),
% 0.20/0.54    inference(subsumption_resolution,[],[f515,f250])).
% 0.20/0.54  fof(f250,plain,(
% 0.20/0.54    sK0 = k1_relat_1(sK2) | ~spl4_24),
% 0.20/0.54    inference(avatar_component_clause,[],[f248])).
% 0.20/0.54  fof(f515,plain,(
% 0.20/0.54    sK0 != k1_relat_1(sK2) | ~v2_funct_1(sK3) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_23 | ~spl4_27 | ~spl4_35)),
% 0.20/0.54    inference(forward_demodulation,[],[f514,f301])).
% 0.20/0.54  fof(f301,plain,(
% 0.20/0.54    sK0 = k2_relat_1(sK3) | ~spl4_27),
% 0.20/0.54    inference(avatar_component_clause,[],[f299])).
% 0.20/0.54  fof(f514,plain,(
% 0.20/0.54    k1_relat_1(sK2) != k2_relat_1(sK3) | ~v2_funct_1(sK3) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_23 | ~spl4_35)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f513])).
% 0.20/0.54  fof(f513,plain,(
% 0.20/0.54    k6_relat_1(sK1) != k6_relat_1(sK1) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v2_funct_1(sK3) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_23 | ~spl4_35)),
% 0.20/0.54    inference(forward_demodulation,[],[f512,f232])).
% 0.20/0.54  fof(f232,plain,(
% 0.20/0.54    sK1 = k1_relat_1(sK3) | ~spl4_23),
% 0.20/0.54    inference(avatar_component_clause,[],[f230])).
% 0.20/0.54  fof(f512,plain,(
% 0.20/0.54    k6_relat_1(k1_relat_1(sK3)) != k6_relat_1(sK1) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v2_funct_1(sK3) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_35)),
% 0.20/0.54    inference(forward_demodulation,[],[f485,f188])).
% 0.20/0.54  fof(f188,plain,(
% 0.20/0.54    sK1 = k2_relat_1(sK2) | ~spl4_18),
% 0.20/0.54    inference(avatar_component_clause,[],[f186])).
% 0.20/0.54  fof(f485,plain,(
% 0.20/0.54    k6_relat_1(k1_relat_1(sK3)) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v2_funct_1(sK3) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_35)),
% 0.20/0.54    inference(subsumption_resolution,[],[f484,f167])).
% 0.20/0.54  fof(f167,plain,(
% 0.20/0.54    v1_relat_1(sK2) | ~spl4_15),
% 0.20/0.54    inference(avatar_component_clause,[],[f165])).
% 0.20/0.54  fof(f484,plain,(
% 0.20/0.54    k6_relat_1(k1_relat_1(sK3)) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK2) | ~v2_funct_1(sK3) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_35)),
% 0.20/0.54    inference(subsumption_resolution,[],[f483,f148])).
% 0.20/0.54  fof(f483,plain,(
% 0.20/0.54    k6_relat_1(k1_relat_1(sK3)) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK3) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_14 | ~spl4_35)),
% 0.20/0.54    inference(subsumption_resolution,[],[f482,f162])).
% 0.20/0.54  fof(f162,plain,(
% 0.20/0.54    v1_relat_1(sK3) | ~spl4_14),
% 0.20/0.54    inference(avatar_component_clause,[],[f160])).
% 0.20/0.54  fof(f482,plain,(
% 0.20/0.54    k6_relat_1(k1_relat_1(sK3)) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK3) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_35)),
% 0.20/0.54    inference(subsumption_resolution,[],[f481,f133])).
% 0.20/0.54  fof(f481,plain,(
% 0.20/0.54    k6_relat_1(k1_relat_1(sK3)) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK3) | (spl4_1 | ~spl4_4 | ~spl4_35)),
% 0.20/0.54    inference(subsumption_resolution,[],[f480,f108])).
% 0.20/0.54  % (30918)Refutation not found, incomplete strategy% (30918)------------------------------
% 0.20/0.54  % (30918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (30918)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (30918)Memory used [KB]: 10746
% 0.20/0.54  % (30918)Time elapsed: 0.138 s
% 0.20/0.54  % (30918)------------------------------
% 0.20/0.54  % (30918)------------------------------
% 0.20/0.54  fof(f108,plain,(
% 0.20/0.54    v2_funct_1(sK2) | ~spl4_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f106])).
% 0.20/0.54  fof(f480,plain,(
% 0.20/0.54    k6_relat_1(k1_relat_1(sK3)) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK3) | (spl4_1 | ~spl4_35)),
% 0.20/0.54    inference(subsumption_resolution,[],[f477,f93])).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    k2_funct_1(sK2) != sK3 | spl4_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f91])).
% 0.20/0.54  fof(f477,plain,(
% 0.20/0.54    k6_relat_1(k1_relat_1(sK3)) != k6_relat_1(k2_relat_1(sK2)) | k2_funct_1(sK2) = sK3 | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK3) | ~spl4_35),
% 0.20/0.54    inference(superposition,[],[f241,f465])).
% 0.20/0.54  fof(f465,plain,(
% 0.20/0.54    sK2 = k2_funct_1(sK3) | ~spl4_35),
% 0.20/0.54    inference(avatar_component_clause,[],[f463])).
% 0.20/0.54  fof(f241,plain,(
% 0.20/0.54    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) != k6_relat_1(k2_relat_1(k2_funct_1(X0))) | k2_funct_1(k2_funct_1(X0)) = X0 | k2_relat_1(X0) != k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f239])).
% 0.20/0.54  fof(f239,plain,(
% 0.20/0.54    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) != k6_relat_1(k2_relat_1(k2_funct_1(X0))) | k2_funct_1(k2_funct_1(X0)) = X0 | k2_relat_1(X0) != k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(superposition,[],[f55,f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_funct_1(X0) = X1 | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 0.20/0.54  fof(f466,plain,(
% 0.20/0.54    spl4_35 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_23 | ~spl4_27 | ~spl4_28 | ~spl4_33),
% 0.20/0.54    inference(avatar_split_clause,[],[f461,f374,f315,f299,f230,f186,f165,f160,f146,f131,f463])).
% 0.20/0.54  fof(f461,plain,(
% 0.20/0.54    sK2 = k2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_23 | ~spl4_27 | ~spl4_28 | ~spl4_33)),
% 0.20/0.54    inference(subsumption_resolution,[],[f460,f188])).
% 0.20/0.54  fof(f460,plain,(
% 0.20/0.54    sK1 != k2_relat_1(sK2) | sK2 = k2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_23 | ~spl4_27 | ~spl4_28 | ~spl4_33)),
% 0.20/0.54    inference(forward_demodulation,[],[f459,f232])).
% 0.20/0.54  fof(f459,plain,(
% 0.20/0.54    sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_27 | ~spl4_28 | ~spl4_33)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f458])).
% 0.20/0.54  fof(f458,plain,(
% 0.20/0.54    k6_relat_1(sK0) != k6_relat_1(sK0) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_27 | ~spl4_28 | ~spl4_33)),
% 0.20/0.54    inference(forward_demodulation,[],[f457,f301])).
% 0.20/0.54  fof(f457,plain,(
% 0.20/0.54    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_28 | ~spl4_33)),
% 0.20/0.54    inference(subsumption_resolution,[],[f456,f162])).
% 0.20/0.54  fof(f456,plain,(
% 0.20/0.54    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_15 | ~spl4_28 | ~spl4_33)),
% 0.20/0.54    inference(subsumption_resolution,[],[f455,f133])).
% 0.20/0.54  fof(f455,plain,(
% 0.20/0.54    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_15 | ~spl4_28 | ~spl4_33)),
% 0.20/0.54    inference(subsumption_resolution,[],[f454,f167])).
% 0.20/0.54  fof(f454,plain,(
% 0.20/0.54    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_28 | ~spl4_33)),
% 0.20/0.54    inference(subsumption_resolution,[],[f453,f148])).
% 0.20/0.54  fof(f453,plain,(
% 0.20/0.54    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_28 | ~spl4_33)),
% 0.20/0.54    inference(subsumption_resolution,[],[f450,f317])).
% 0.20/0.54  fof(f317,plain,(
% 0.20/0.54    v2_funct_1(sK3) | ~spl4_28),
% 0.20/0.54    inference(avatar_component_clause,[],[f315])).
% 0.20/0.54  fof(f450,plain,(
% 0.20/0.54    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_33),
% 0.20/0.54    inference(superposition,[],[f55,f376])).
% 0.20/0.54  fof(f416,plain,(
% 0.20/0.54    spl4_33 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_31),
% 0.20/0.54    inference(avatar_split_clause,[],[f415,f365,f146,f136,f131,f121,f374])).
% 0.20/0.54  fof(f365,plain,(
% 0.20/0.54    spl4_31 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.20/0.54  fof(f415,plain,(
% 0.20/0.54    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_31)),
% 0.20/0.54    inference(subsumption_resolution,[],[f414,f148])).
% 0.20/0.54  fof(f414,plain,(
% 0.20/0.54    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_31)),
% 0.20/0.54    inference(subsumption_resolution,[],[f413,f138])).
% 0.20/0.54  fof(f413,plain,(
% 0.20/0.54    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_31)),
% 0.20/0.54    inference(subsumption_resolution,[],[f412,f133])).
% 0.20/0.54  fof(f412,plain,(
% 0.20/0.54    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_31)),
% 0.20/0.54    inference(subsumption_resolution,[],[f404,f123])).
% 0.20/0.54  fof(f404,plain,(
% 0.20/0.54    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_31),
% 0.20/0.54    inference(superposition,[],[f76,f367])).
% 0.20/0.54  fof(f367,plain,(
% 0.20/0.54    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl4_31),
% 0.20/0.54    inference(avatar_component_clause,[],[f365])).
% 0.20/0.54  fof(f396,plain,(
% 0.20/0.54    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_30),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f395])).
% 0.20/0.54  fof(f395,plain,(
% 0.20/0.54    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_30)),
% 0.20/0.54    inference(subsumption_resolution,[],[f394,f148])).
% 0.20/0.54  fof(f394,plain,(
% 0.20/0.54    ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | spl4_30)),
% 0.20/0.54    inference(subsumption_resolution,[],[f393,f138])).
% 0.20/0.54  fof(f393,plain,(
% 0.20/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | spl4_30)),
% 0.20/0.54    inference(subsumption_resolution,[],[f392,f133])).
% 0.20/0.54  fof(f392,plain,(
% 0.20/0.54    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | spl4_30)),
% 0.20/0.54    inference(subsumption_resolution,[],[f389,f123])).
% 0.20/0.54  fof(f389,plain,(
% 0.20/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_30),
% 0.20/0.54    inference(resolution,[],[f363,f75])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.54    inference(flattening,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.20/0.54  fof(f363,plain,(
% 0.20/0.54    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_30),
% 0.20/0.54    inference(avatar_component_clause,[],[f361])).
% 0.20/0.54  fof(f361,plain,(
% 0.20/0.54    spl4_30 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.20/0.54  fof(f368,plain,(
% 0.20/0.54    ~spl4_30 | spl4_31 | ~spl4_13),
% 0.20/0.54    inference(avatar_split_clause,[],[f357,f152,f365,f361])).
% 0.20/0.54  fof(f152,plain,(
% 0.20/0.54    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.54  fof(f357,plain,(
% 0.20/0.54    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_13),
% 0.20/0.54    inference(resolution,[],[f238,f154])).
% 0.20/0.54  fof(f154,plain,(
% 0.20/0.54    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 0.20/0.54    inference(avatar_component_clause,[],[f152])).
% 0.20/0.54  fof(f238,plain,(
% 0.20/0.54    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 0.20/0.54    inference(resolution,[],[f70,f79])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(flattening,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.20/0.54  fof(f304,plain,(
% 0.20/0.54    spl4_27 | ~spl4_7 | ~spl4_26),
% 0.20/0.54    inference(avatar_split_clause,[],[f303,f291,f121,f299])).
% 0.20/0.54  fof(f291,plain,(
% 0.20/0.54    spl4_26 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.54  fof(f303,plain,(
% 0.20/0.54    sK0 = k2_relat_1(sK3) | (~spl4_7 | ~spl4_26)),
% 0.20/0.54    inference(subsumption_resolution,[],[f296,f123])).
% 0.20/0.54  fof(f296,plain,(
% 0.20/0.54    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_26),
% 0.20/0.54    inference(superposition,[],[f77,f293])).
% 0.20/0.54  fof(f293,plain,(
% 0.20/0.54    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_26),
% 0.20/0.54    inference(avatar_component_clause,[],[f291])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  % (30910)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (30919)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (30912)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  % (30912)Refutation not found, incomplete strategy% (30912)------------------------------
% 0.20/0.55  % (30912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (30912)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (30912)Memory used [KB]: 11001
% 0.20/0.55  % (30912)Time elapsed: 0.143 s
% 0.20/0.55  % (30912)------------------------------
% 0.20/0.55  % (30912)------------------------------
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.55  fof(f294,plain,(
% 0.20/0.55    spl4_26 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13),
% 0.20/0.55    inference(avatar_split_clause,[],[f289,f152,f146,f141,f136,f131,f126,f121,f291])).
% 0.20/0.55  fof(f289,plain,(
% 0.20/0.55    sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 0.20/0.55    inference(subsumption_resolution,[],[f288,f133])).
% 0.20/0.55  fof(f288,plain,(
% 0.20/0.55    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 0.20/0.55    inference(subsumption_resolution,[],[f287,f128])).
% 0.20/0.55  fof(f287,plain,(
% 0.20/0.55    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 0.20/0.55    inference(subsumption_resolution,[],[f286,f123])).
% 0.20/0.55  fof(f286,plain,(
% 0.20/0.55    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 0.20/0.55    inference(subsumption_resolution,[],[f285,f148])).
% 0.20/0.55  fof(f285,plain,(
% 0.20/0.55    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_13)),
% 0.20/0.55    inference(subsumption_resolution,[],[f284,f143])).
% 0.20/0.55  fof(f284,plain,(
% 0.20/0.55    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_13)),
% 0.20/0.55    inference(subsumption_resolution,[],[f281,f138])).
% 0.20/0.55  fof(f281,plain,(
% 0.20/0.55    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_13),
% 0.20/0.55    inference(resolution,[],[f280,f154])).
% 0.20/0.55  fof(f280,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f72,f73])).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.55    inference(flattening,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 0.20/0.55  fof(f253,plain,(
% 0.20/0.55    spl4_24 | ~spl4_10 | ~spl4_22),
% 0.20/0.55    inference(avatar_split_clause,[],[f252,f218,f136,f248])).
% 0.20/0.55  fof(f218,plain,(
% 0.20/0.55    spl4_22 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.55  fof(f252,plain,(
% 0.20/0.55    sK0 = k1_relat_1(sK2) | (~spl4_10 | ~spl4_22)),
% 0.20/0.55    inference(subsumption_resolution,[],[f244,f138])).
% 0.20/0.55  fof(f244,plain,(
% 0.20/0.55    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_22),
% 0.20/0.55    inference(superposition,[],[f80,f220])).
% 0.20/0.55  fof(f220,plain,(
% 0.20/0.55    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_22),
% 0.20/0.55    inference(avatar_component_clause,[],[f218])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.55  fof(f235,plain,(
% 0.20/0.55    spl4_23 | ~spl4_7 | ~spl4_21),
% 0.20/0.55    inference(avatar_split_clause,[],[f234,f211,f121,f230])).
% 0.20/0.55  fof(f211,plain,(
% 0.20/0.55    spl4_21 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.55  fof(f234,plain,(
% 0.20/0.55    sK1 = k1_relat_1(sK3) | (~spl4_7 | ~spl4_21)),
% 0.20/0.55    inference(subsumption_resolution,[],[f226,f123])).
% 0.20/0.55  fof(f226,plain,(
% 0.20/0.55    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_21),
% 0.20/0.55    inference(superposition,[],[f80,f213])).
% 0.20/0.55  fof(f213,plain,(
% 0.20/0.55    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_21),
% 0.20/0.55    inference(avatar_component_clause,[],[f211])).
% 0.20/0.55  fof(f221,plain,(
% 0.20/0.55    spl4_22 | spl4_2 | ~spl4_10 | ~spl4_11),
% 0.20/0.55    inference(avatar_split_clause,[],[f216,f141,f136,f96,f218])).
% 0.20/0.55  fof(f96,plain,(
% 0.20/0.55    spl4_2 <=> k1_xboole_0 = sK1),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.55  fof(f216,plain,(
% 0.20/0.55    sK0 = k1_relset_1(sK0,sK1,sK2) | (spl4_2 | ~spl4_10 | ~spl4_11)),
% 0.20/0.55    inference(subsumption_resolution,[],[f215,f98])).
% 0.20/0.55  fof(f98,plain,(
% 0.20/0.55    k1_xboole_0 != sK1 | spl4_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f96])).
% 0.20/0.55  fof(f215,plain,(
% 0.20/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl4_10 | ~spl4_11)),
% 0.20/0.55    inference(subsumption_resolution,[],[f206,f143])).
% 0.20/0.55  fof(f206,plain,(
% 0.20/0.55    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_10),
% 0.20/0.55    inference(resolution,[],[f62,f138])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(nnf_transformation,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(flattening,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.55  fof(f214,plain,(
% 0.20/0.55    spl4_21 | spl4_3 | ~spl4_7 | ~spl4_8),
% 0.20/0.55    inference(avatar_split_clause,[],[f209,f126,f121,f101,f211])).
% 0.20/0.55  fof(f209,plain,(
% 0.20/0.55    sK1 = k1_relset_1(sK1,sK0,sK3) | (spl4_3 | ~spl4_7 | ~spl4_8)),
% 0.20/0.55    inference(subsumption_resolution,[],[f208,f103])).
% 0.20/0.55  fof(f208,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8)),
% 0.20/0.55    inference(subsumption_resolution,[],[f205,f128])).
% 0.20/0.55  fof(f205,plain,(
% 0.20/0.55    ~v1_funct_2(sK3,sK1,sK0) | k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_7),
% 0.20/0.55    inference(resolution,[],[f62,f123])).
% 0.20/0.55  fof(f191,plain,(
% 0.20/0.55    spl4_18 | ~spl4_6 | ~spl4_10),
% 0.20/0.55    inference(avatar_split_clause,[],[f190,f136,f116,f186])).
% 0.20/0.55  fof(f190,plain,(
% 0.20/0.55    sK1 = k2_relat_1(sK2) | (~spl4_6 | ~spl4_10)),
% 0.20/0.55    inference(subsumption_resolution,[],[f183,f138])).
% 0.20/0.55  fof(f183,plain,(
% 0.20/0.55    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 0.20/0.55    inference(superposition,[],[f118,f77])).
% 0.20/0.55  fof(f168,plain,(
% 0.20/0.55    spl4_15 | ~spl4_10),
% 0.20/0.55    inference(avatar_split_clause,[],[f157,f136,f165])).
% 0.20/0.55  fof(f157,plain,(
% 0.20/0.55    v1_relat_1(sK2) | ~spl4_10),
% 0.20/0.55    inference(resolution,[],[f78,f138])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.55  fof(f163,plain,(
% 0.20/0.55    spl4_14 | ~spl4_7),
% 0.20/0.55    inference(avatar_split_clause,[],[f156,f121,f160])).
% 0.20/0.55  fof(f156,plain,(
% 0.20/0.55    v1_relat_1(sK3) | ~spl4_7),
% 0.20/0.55    inference(resolution,[],[f78,f123])).
% 0.20/0.55  fof(f155,plain,(
% 0.20/0.55    spl4_13 | ~spl4_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f150,f111,f152])).
% 0.20/0.55  fof(f111,plain,(
% 0.20/0.55    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.55  fof(f150,plain,(
% 0.20/0.55    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 0.20/0.55    inference(backward_demodulation,[],[f113,f73])).
% 0.20/0.55  fof(f113,plain,(
% 0.20/0.55    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f111])).
% 0.20/0.55  fof(f149,plain,(
% 0.20/0.55    spl4_12),
% 0.20/0.55    inference(avatar_split_clause,[],[f43,f146])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    v1_funct_1(sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f39,f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.55    inference(flattening,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.20/0.55    inference(negated_conjecture,[],[f15])).
% 0.20/0.55  fof(f15,conjecture,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 0.20/0.55  fof(f144,plain,(
% 0.20/0.55    spl4_11),
% 0.20/0.55    inference(avatar_split_clause,[],[f44,f141])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f139,plain,(
% 0.20/0.55    spl4_10),
% 0.20/0.55    inference(avatar_split_clause,[],[f45,f136])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f134,plain,(
% 0.20/0.55    spl4_9),
% 0.20/0.55    inference(avatar_split_clause,[],[f46,f131])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    v1_funct_1(sK3)),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f129,plain,(
% 0.20/0.55    spl4_8),
% 0.20/0.55    inference(avatar_split_clause,[],[f47,f126])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f124,plain,(
% 0.20/0.55    spl4_7),
% 0.20/0.55    inference(avatar_split_clause,[],[f48,f121])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f119,plain,(
% 0.20/0.55    spl4_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f49,f116])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f114,plain,(
% 0.20/0.55    spl4_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f50,f111])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f109,plain,(
% 0.20/0.55    spl4_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f51,f106])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    v2_funct_1(sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f104,plain,(
% 0.20/0.55    ~spl4_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f52,f101])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    k1_xboole_0 != sK0),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f99,plain,(
% 0.20/0.55    ~spl4_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f53,f96])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    k1_xboole_0 != sK1),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f94,plain,(
% 0.20/0.55    ~spl4_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f54,f91])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    k2_funct_1(sK2) != sK3),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (30923)------------------------------
% 0.20/0.55  % (30923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (30923)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (30923)Memory used [KB]: 6652
% 0.20/0.55  % (30923)Time elapsed: 0.124 s
% 0.20/0.55  % (30923)------------------------------
% 0.20/0.55  % (30923)------------------------------
% 0.20/0.55  % (30900)Success in time 0.198 s
%------------------------------------------------------------------------------
