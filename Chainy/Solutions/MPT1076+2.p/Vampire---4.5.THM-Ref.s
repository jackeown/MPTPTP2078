%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1076+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:05 EST 2020

% Result     : Theorem 6.16s
% Output     : Refutation 6.16s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 318 expanded)
%              Number of leaves         :   27 ( 160 expanded)
%              Depth                    :    8
%              Number of atoms          :  486 (1870 expanded)
%              Number of equality atoms :   42 ( 196 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10933,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4194,f4199,f4204,f4209,f4214,f4219,f4224,f4234,f4239,f4249,f4691,f4772,f4816,f6714,f10922,f10932])).

fof(f10932,plain,
    ( spl235_1
    | ~ spl235_4
    | ~ spl235_10
    | spl235_31
    | spl235_38
    | ~ spl235_71
    | ~ spl235_84 ),
    inference(avatar_contradiction_clause,[],[f10931])).

fof(f10931,plain,
    ( $false
    | spl235_1
    | ~ spl235_4
    | ~ spl235_10
    | spl235_31
    | spl235_38
    | ~ spl235_71
    | ~ spl235_84 ),
    inference(subsumption_resolution,[],[f10930,f4771])).

fof(f4771,plain,
    ( k7_partfun1(sK4,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | spl235_31 ),
    inference(avatar_component_clause,[],[f4769])).

fof(f4769,plain,
    ( spl235_31
  <=> k7_partfun1(sK4,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl235_31])])).

fof(f10930,plain,
    ( k7_partfun1(sK4,sK6,k1_funct_1(sK5,sK7)) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | spl235_1
    | ~ spl235_4
    | ~ spl235_10
    | spl235_38
    | ~ spl235_71
    | ~ spl235_84 ),
    inference(forward_demodulation,[],[f10923,f10924])).

fof(f10924,plain,
    ( k1_funct_1(sK6,k1_funct_1(sK5,sK7)) = k3_funct_2(sK2,sK4,sK6,k1_funct_1(sK5,sK7))
    | spl235_1
    | ~ spl235_4
    | ~ spl235_10
    | ~ spl235_71
    | ~ spl235_84 ),
    inference(unit_resulting_resolution,[],[f4193,f4208,f6713,f4238,f10921,f2765])).

fof(f2765,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1705])).

fof(f1705,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1704])).

fof(f1704,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1541])).

fof(f1541,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f10921,plain,
    ( m1_subset_1(k1_funct_1(sK5,sK7),sK2)
    | ~ spl235_84 ),
    inference(avatar_component_clause,[],[f10919])).

fof(f10919,plain,
    ( spl235_84
  <=> m1_subset_1(k1_funct_1(sK5,sK7),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl235_84])])).

fof(f4238,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ spl235_10 ),
    inference(avatar_component_clause,[],[f4236])).

fof(f4236,plain,
    ( spl235_10
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl235_10])])).

fof(f6713,plain,
    ( v1_funct_2(sK6,sK2,sK4)
    | ~ spl235_71 ),
    inference(avatar_component_clause,[],[f6711])).

fof(f6711,plain,
    ( spl235_71
  <=> v1_funct_2(sK6,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl235_71])])).

fof(f4208,plain,
    ( v1_funct_1(sK6)
    | ~ spl235_4 ),
    inference(avatar_component_clause,[],[f4206])).

fof(f4206,plain,
    ( spl235_4
  <=> v1_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl235_4])])).

fof(f4193,plain,
    ( ~ v1_xboole_0(sK2)
    | spl235_1 ),
    inference(avatar_component_clause,[],[f4191])).

fof(f4191,plain,
    ( spl235_1
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl235_1])])).

fof(f10923,plain,
    ( k7_partfun1(sK4,sK6,k1_funct_1(sK5,sK7)) = k3_funct_2(sK2,sK4,sK6,k1_funct_1(sK5,sK7))
    | spl235_1
    | ~ spl235_4
    | ~ spl235_10
    | spl235_38
    | ~ spl235_71
    | ~ spl235_84 ),
    inference(unit_resulting_resolution,[],[f4193,f4815,f4208,f6713,f4238,f10921,f2760])).

fof(f2760,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1695])).

fof(f1695,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1694])).

fof(f1694,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1531])).

fof(f1531,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',ie1_funct_2)).

fof(f4815,plain,
    ( ~ v1_xboole_0(sK4)
    | spl235_38 ),
    inference(avatar_component_clause,[],[f4813])).

fof(f4813,plain,
    ( spl235_38
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl235_38])])).

fof(f10922,plain,
    ( spl235_84
    | spl235_2
    | ~ spl235_3
    | ~ spl235_5
    | ~ spl235_7
    | ~ spl235_9 ),
    inference(avatar_split_clause,[],[f4684,f4231,f4221,f4211,f4201,f4196,f10919])).

fof(f4196,plain,
    ( spl235_2
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl235_2])])).

fof(f4201,plain,
    ( spl235_3
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl235_3])])).

fof(f4211,plain,
    ( spl235_5
  <=> m1_subset_1(sK7,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl235_5])])).

fof(f4221,plain,
    ( spl235_7
  <=> v1_funct_2(sK5,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl235_7])])).

fof(f4231,plain,
    ( spl235_9
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl235_9])])).

fof(f4684,plain,
    ( m1_subset_1(k1_funct_1(sK5,sK7),sK2)
    | spl235_2
    | ~ spl235_3
    | ~ spl235_5
    | ~ spl235_7
    | ~ spl235_9 ),
    inference(backward_demodulation,[],[f4642,f4681])).

fof(f4681,plain,
    ( k3_funct_2(sK3,sK2,sK5,sK7) = k1_funct_1(sK5,sK7)
    | spl235_2
    | ~ spl235_3
    | ~ spl235_5
    | ~ spl235_7
    | ~ spl235_9 ),
    inference(unit_resulting_resolution,[],[f4198,f4203,f4213,f4223,f4233,f2765])).

fof(f4233,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ spl235_9 ),
    inference(avatar_component_clause,[],[f4231])).

fof(f4223,plain,
    ( v1_funct_2(sK5,sK3,sK2)
    | ~ spl235_7 ),
    inference(avatar_component_clause,[],[f4221])).

fof(f4213,plain,
    ( m1_subset_1(sK7,sK3)
    | ~ spl235_5 ),
    inference(avatar_component_clause,[],[f4211])).

fof(f4203,plain,
    ( v1_funct_1(sK5)
    | ~ spl235_3 ),
    inference(avatar_component_clause,[],[f4201])).

fof(f4198,plain,
    ( ~ v1_xboole_0(sK3)
    | spl235_2 ),
    inference(avatar_component_clause,[],[f4196])).

fof(f4642,plain,
    ( m1_subset_1(k3_funct_2(sK3,sK2,sK5,sK7),sK2)
    | spl235_2
    | ~ spl235_3
    | ~ spl235_5
    | ~ spl235_7
    | ~ spl235_9 ),
    inference(unit_resulting_resolution,[],[f4198,f4203,f4213,f4223,f4233,f2766])).

fof(f2766,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1707])).

fof(f1707,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1706])).

fof(f1706,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1494])).

fof(f1494,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(f6714,plain,
    ( spl235_71
    | ~ spl235_4
    | ~ spl235_6
    | ~ spl235_10 ),
    inference(avatar_split_clause,[],[f4569,f4236,f4216,f4206,f6711])).

fof(f4216,plain,
    ( spl235_6
  <=> v1_partfun1(sK6,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl235_6])])).

fof(f4569,plain,
    ( v1_funct_2(sK6,sK2,sK4)
    | ~ spl235_4
    | ~ spl235_6
    | ~ spl235_10 ),
    inference(unit_resulting_resolution,[],[f4208,f4218,f4238,f2791])).

fof(f2791,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f1729])).

fof(f1729,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f1728])).

fof(f1728,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1560])).

fof(f1560,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_funct_2)).

fof(f4218,plain,
    ( v1_partfun1(sK6,sK2)
    | ~ spl235_6 ),
    inference(avatar_component_clause,[],[f4216])).

fof(f4816,plain,
    ( ~ spl235_38
    | spl235_1
    | ~ spl235_6
    | ~ spl235_10 ),
    inference(avatar_split_clause,[],[f4546,f4236,f4216,f4191,f4813])).

fof(f4546,plain,
    ( ~ v1_xboole_0(sK4)
    | spl235_1
    | ~ spl235_6
    | ~ spl235_10 ),
    inference(unit_resulting_resolution,[],[f4193,f4218,f4238,f2797])).

fof(f2797,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1735])).

fof(f1735,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1734])).

fof(f1734,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1471])).

fof(f1471,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).

fof(f4772,plain,
    ( ~ spl235_31
    | spl235_1
    | spl235_2
    | ~ spl235_3
    | ~ spl235_4
    | ~ spl235_5
    | ~ spl235_6
    | ~ spl235_7
    | ~ spl235_9
    | ~ spl235_10
    | spl235_27 ),
    inference(avatar_split_clause,[],[f4763,f4688,f4236,f4231,f4221,f4216,f4211,f4206,f4201,f4196,f4191,f4769])).

fof(f4688,plain,
    ( spl235_27
  <=> k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) = k7_partfun1(sK4,sK6,k1_funct_1(sK5,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl235_27])])).

fof(f4763,plain,
    ( k7_partfun1(sK4,sK6,k1_funct_1(sK5,sK7)) != k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | spl235_1
    | spl235_2
    | ~ spl235_3
    | ~ spl235_4
    | ~ spl235_5
    | ~ spl235_6
    | ~ spl235_7
    | ~ spl235_9
    | ~ spl235_10
    | spl235_27 ),
    inference(backward_demodulation,[],[f4690,f4762])).

fof(f4762,plain,
    ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) = k1_funct_1(sK6,k1_funct_1(sK5,sK7))
    | spl235_1
    | spl235_2
    | ~ spl235_3
    | ~ spl235_4
    | ~ spl235_5
    | ~ spl235_6
    | ~ spl235_7
    | ~ spl235_9
    | ~ spl235_10 ),
    inference(forward_demodulation,[],[f4759,f4681])).

fof(f4759,plain,
    ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) = k1_funct_1(sK6,k3_funct_2(sK3,sK2,sK5,sK7))
    | spl235_1
    | spl235_2
    | ~ spl235_3
    | ~ spl235_4
    | ~ spl235_5
    | ~ spl235_6
    | ~ spl235_7
    | ~ spl235_9
    | ~ spl235_10 ),
    inference(unit_resulting_resolution,[],[f4193,f4198,f4203,f4208,f4213,f4218,f4223,f4233,f4238,f2775])).

fof(f2775,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(X3,X1,X0)
      | ~ v1_partfun1(X4,X0)
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1719])).

fof(f1719,plain,(
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
    inference(flattening,[],[f1718])).

fof(f1718,plain,(
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
    inference(ennf_transformation,[],[f1621])).

fof(f1621,axiom,(
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

fof(f4690,plain,
    ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) != k7_partfun1(sK4,sK6,k1_funct_1(sK5,sK7))
    | spl235_27 ),
    inference(avatar_component_clause,[],[f4688])).

fof(f4691,plain,
    ( ~ spl235_27
    | spl235_2
    | ~ spl235_3
    | ~ spl235_5
    | ~ spl235_7
    | ~ spl235_9
    | spl235_12 ),
    inference(avatar_split_clause,[],[f4686,f4246,f4231,f4221,f4211,f4201,f4196,f4688])).

fof(f4246,plain,
    ( spl235_12
  <=> k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) = k7_partfun1(sK4,sK6,k3_funct_2(sK3,sK2,sK5,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl235_12])])).

fof(f4686,plain,
    ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) != k7_partfun1(sK4,sK6,k1_funct_1(sK5,sK7))
    | spl235_2
    | ~ spl235_3
    | ~ spl235_5
    | ~ spl235_7
    | ~ spl235_9
    | spl235_12 ),
    inference(backward_demodulation,[],[f4248,f4681])).

fof(f4248,plain,
    ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) != k7_partfun1(sK4,sK6,k3_funct_2(sK3,sK2,sK5,sK7))
    | spl235_12 ),
    inference(avatar_component_clause,[],[f4246])).

fof(f4249,plain,(
    ~ spl235_12 ),
    inference(avatar_split_clause,[],[f2759,f4246])).

fof(f2759,plain,(
    k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) != k7_partfun1(sK4,sK6,k3_funct_2(sK3,sK2,sK5,sK7)) ),
    inference(cnf_transformation,[],[f2346])).

fof(f2346,plain,
    ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) != k7_partfun1(sK4,sK6,k3_funct_2(sK3,sK2,sK5,sK7))
    & v1_partfun1(sK6,sK2)
    & m1_subset_1(sK7,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    & v1_funct_2(sK5,sK3,sK2)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f1693,f2345,f2344,f2343,f2342,f2341])).

fof(f2341,plain,
    ( ? [X0] :
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
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,sK2,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK2,X3,X5))
                      & v1_partfun1(X4,sK2)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
              & v1_funct_2(X3,X1,sK2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f2342,plain,
    ( ? [X1] :
        ( ? [X3,X2] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k3_funct_2(X1,X2,k8_funct_2(X1,sK2,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK2,X3,X5))
                    & v1_partfun1(X4,sK2)
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
            & v1_funct_2(X3,X1,sK2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X3,X2] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k3_funct_2(sK3,X2,k8_funct_2(sK3,sK2,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK3,sK2,X3,X5))
                  & v1_partfun1(X4,sK2)
                  & m1_subset_1(X5,sK3) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
          & v1_funct_2(X3,sK3,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f2343,plain,
    ( ? [X3,X2] :
        ( ? [X4] :
            ( ? [X5] :
                ( k3_funct_2(sK3,X2,k8_funct_2(sK3,sK2,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK3,sK2,X3,X5))
                & v1_partfun1(X4,sK2)
                & m1_subset_1(X5,sK3) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X2)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
        & v1_funct_2(X3,sK3,sK2)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,X4),X5) != k7_partfun1(sK4,X4,k3_funct_2(sK3,sK2,sK5,X5))
              & v1_partfun1(X4,sK2)
              & m1_subset_1(X5,sK3) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      & v1_funct_2(sK5,sK3,sK2)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f2344,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,X4),X5) != k7_partfun1(sK4,X4,k3_funct_2(sK3,sK2,sK5,X5))
            & v1_partfun1(X4,sK2)
            & m1_subset_1(X5,sK3) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),X5) != k7_partfun1(sK4,sK6,k3_funct_2(sK3,sK2,sK5,X5))
          & v1_partfun1(sK6,sK2)
          & m1_subset_1(X5,sK3) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f2345,plain,
    ( ? [X5] :
        ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),X5) != k7_partfun1(sK4,sK6,k3_funct_2(sK3,sK2,sK5,X5))
        & v1_partfun1(sK6,sK2)
        & m1_subset_1(X5,sK3) )
   => ( k3_funct_2(sK3,sK4,k8_funct_2(sK3,sK2,sK4,sK5,sK6),sK7) != k7_partfun1(sK4,sK6,k3_funct_2(sK3,sK2,sK5,sK7))
      & v1_partfun1(sK6,sK2)
      & m1_subset_1(sK7,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f1693,plain,(
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
    inference(flattening,[],[f1692])).

fof(f1692,plain,(
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
    inference(ennf_transformation,[],[f1623])).

fof(f1623,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1622])).

fof(f1622,conjecture,(
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

fof(f4239,plain,(
    spl235_10 ),
    inference(avatar_split_clause,[],[f2756,f4236])).

fof(f2756,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) ),
    inference(cnf_transformation,[],[f2346])).

fof(f4234,plain,(
    spl235_9 ),
    inference(avatar_split_clause,[],[f2754,f4231])).

fof(f2754,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f2346])).

fof(f4224,plain,(
    spl235_7 ),
    inference(avatar_split_clause,[],[f2753,f4221])).

fof(f2753,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f2346])).

fof(f4219,plain,(
    spl235_6 ),
    inference(avatar_split_clause,[],[f2758,f4216])).

fof(f2758,plain,(
    v1_partfun1(sK6,sK2) ),
    inference(cnf_transformation,[],[f2346])).

fof(f4214,plain,(
    spl235_5 ),
    inference(avatar_split_clause,[],[f2757,f4211])).

fof(f2757,plain,(
    m1_subset_1(sK7,sK3) ),
    inference(cnf_transformation,[],[f2346])).

fof(f4209,plain,(
    spl235_4 ),
    inference(avatar_split_clause,[],[f2755,f4206])).

fof(f2755,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f2346])).

fof(f4204,plain,(
    spl235_3 ),
    inference(avatar_split_clause,[],[f2752,f4201])).

fof(f2752,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f2346])).

fof(f4199,plain,(
    ~ spl235_2 ),
    inference(avatar_split_clause,[],[f2751,f4196])).

fof(f2751,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f2346])).

fof(f4194,plain,(
    ~ spl235_1 ),
    inference(avatar_split_clause,[],[f2750,f4191])).

fof(f2750,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f2346])).
%------------------------------------------------------------------------------
