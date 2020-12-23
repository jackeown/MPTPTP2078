%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 232 expanded)
%              Number of leaves         :   22 ( 103 expanded)
%              Depth                    :   11
%              Number of atoms          :  401 ( 931 expanded)
%              Number of equality atoms :  210 ( 609 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f41,f46,f51,f65,f78,f87,f105,f111,f116,f121,f129,f136,f152,f163,f171])).

fof(f171,plain,
    ( spl7_8
    | ~ spl7_11
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl7_8
    | ~ spl7_11
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f164,f73])).

fof(f73,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) != sK5
    | spl7_8 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl7_8
  <=> k6_mcart_1(sK0,sK1,sK2,sK3) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f164,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = sK5
    | ~ spl7_11
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(backward_demodulation,[],[f120,f148])).

fof(f148,plain,
    ( sK5 = k2_mcart_1(k1_mcart_1(sK3))
    | ~ spl7_11
    | ~ spl7_16 ),
    inference(trivial_inequality_removal,[],[f145])).

fof(f145,plain,
    ( sK3 != sK3
    | sK5 = k2_mcart_1(k1_mcart_1(sK3))
    | ~ spl7_11
    | ~ spl7_16 ),
    inference(superposition,[],[f98,f135])).

fof(f135,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl7_16
  <=> sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f98,plain,
    ( ! [X2,X0,X1] :
        ( k3_mcart_1(X0,X1,X2) != sK3
        | sK5 = X1 )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl7_11
  <=> ! [X1,X0,X2] :
        ( k3_mcart_1(X0,X1,X2) != sK3
        | sK5 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f120,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl7_14
  <=> k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f163,plain,
    ( spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f155,f133,f108,f84,f75])).

fof(f75,plain,
    ( spl7_9
  <=> k7_mcart_1(sK0,sK1,sK2,sK3) = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f84,plain,
    ( spl7_10
  <=> k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f108,plain,
    ( spl7_12
  <=> ! [X1,X0,X2] :
        ( k3_mcart_1(X0,X1,X2) != sK3
        | sK6 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f155,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = sK6
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(backward_demodulation,[],[f86,f147])).

fof(f147,plain,
    ( sK6 = k2_mcart_1(sK3)
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(trivial_inequality_removal,[],[f146])).

fof(f146,plain,
    ( sK3 != sK3
    | sK6 = k2_mcart_1(sK3)
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(superposition,[],[f109,f135])).

fof(f109,plain,
    ( ! [X2,X0,X1] :
        ( k3_mcart_1(X0,X1,X2) != sK3
        | sK6 = X2 )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f108])).

fof(f86,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f84])).

fof(f152,plain,
    ( ~ spl7_6
    | spl7_15
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl7_6
    | spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f149,f128])).

fof(f128,plain,
    ( sK4 != k1_mcart_1(k1_mcart_1(sK3))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl7_15
  <=> sK4 = k1_mcart_1(k1_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f149,plain,
    ( sK4 = k1_mcart_1(k1_mcart_1(sK3))
    | ~ spl7_6
    | ~ spl7_16 ),
    inference(trivial_inequality_removal,[],[f144])).

fof(f144,plain,
    ( sK3 != sK3
    | sK4 = k1_mcart_1(k1_mcart_1(sK3))
    | ~ spl7_6
    | ~ spl7_16 ),
    inference(superposition,[],[f60,f135])).

fof(f60,plain,
    ( ! [X2,X0,X1] :
        ( k3_mcart_1(X0,X1,X2) != sK3
        | sK4 = X0 )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl7_6
  <=> ! [X1,X0,X2] :
        ( k3_mcart_1(X0,X1,X2) != sK3
        | sK4 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f136,plain,
    ( spl7_16
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_13
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f131,f118,f113,f84,f43,f38,f33,f28,f133])).

fof(f28,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f33,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f38,plain,
    ( spl7_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f43,plain,
    ( spl7_4
  <=> m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f113,plain,
    ( spl7_13
  <=> k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f131,plain,
    ( sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3))
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_13
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f130,f115])).

fof(f115,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f113])).

fof(f130,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3))
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f104,f120])).

fof(f104,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k2_mcart_1(sK3))
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f103,f86])).

fof(f103,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f102,f30])).

fof(f30,plain,
    ( k1_xboole_0 != sK0
    | spl7_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f102,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0
    | spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f101,f35])).

fof(f35,plain,
    ( k1_xboole_0 != sK1
    | spl7_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f101,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f100,f40])).

fof(f40,plain,
    ( k1_xboole_0 != sK2
    | spl7_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f100,plain,
    ( sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_4 ),
    inference(resolution,[],[f20,f45])).

fof(f45,plain,
    ( m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f129,plain,
    ( ~ spl7_15
    | spl7_7
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f124,f113,f67,f126])).

fof(f67,plain,
    ( spl7_7
  <=> k5_mcart_1(sK0,sK1,sK2,sK3) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f124,plain,
    ( sK4 != k1_mcart_1(k1_mcart_1(sK3))
    | spl7_7
    | ~ spl7_13 ),
    inference(superposition,[],[f69,f115])).

fof(f69,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) != sK4
    | spl7_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f121,plain,
    ( spl7_14
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f95,f43,f38,f33,f28,f118])).

fof(f95,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f94,f30])).

fof(f94,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK0
    | spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f93,f35])).

fof(f93,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f92,f40])).

fof(f92,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_4 ),
    inference(resolution,[],[f22,f45])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f116,plain,
    ( spl7_13
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f91,f43,f38,f33,f28,f113])).

fof(f91,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f90,f30])).

fof(f90,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK0
    | spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f89,f35])).

fof(f89,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f88,f40])).

fof(f88,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_4 ),
    inference(resolution,[],[f21,f45])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f111,plain,
    ( spl7_12
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f63,f48,f108])).

fof(f48,plain,
    ( spl7_5
  <=> sK3 = k3_mcart_1(sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f63,plain,
    ( ! [X2,X0,X1] :
        ( k3_mcart_1(X0,X1,X2) != sK3
        | sK6 = X2 )
    | ~ spl7_5 ),
    inference(superposition,[],[f26,f50])).

fof(f50,plain,
    ( sK3 = k3_mcart_1(sK4,sK5,sK6)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)
      | X2 = X5 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5)
     => ( X2 = X5
        & X1 = X4
        & X0 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).

fof(f105,plain,
    ( spl7_11
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f56,f48,f97])).

fof(f56,plain,
    ( ! [X2,X0,X1] :
        ( k3_mcart_1(X0,X1,X2) != sK3
        | sK5 = X1 )
    | ~ spl7_5 ),
    inference(superposition,[],[f25,f50])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)
      | X1 = X4 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f87,plain,
    ( spl7_10
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f82,f43,f38,f33,f28,f84])).

fof(f82,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f81,f30])).

fof(f81,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | k1_xboole_0 = sK0
    | spl7_2
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f80,f35])).

fof(f80,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f79,f40])).

fof(f79,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_4 ),
    inference(resolution,[],[f23,f45])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f78,plain,
    ( ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f19,f75,f71,f67])).

fof(f19,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK3) != sK6
    | k6_mcart_1(sK0,sK1,sK2,sK3) != sK5
    | k5_mcart_1(sK0,sK1,sK2,sK3) != sK4 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( k7_mcart_1(sK0,sK1,sK2,sK3) != sK6
      | k6_mcart_1(sK0,sK1,sK2,sK3) != sK5
      | k5_mcart_1(sK0,sK1,sK2,sK3) != sK4 )
    & sK3 = k3_mcart_1(sK4,sK5,sK6)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4,X5,X6] :
            ( ( k7_mcart_1(X0,X1,X2,X3) != X6
              | k6_mcart_1(X0,X1,X2,X3) != X5
              | k5_mcart_1(X0,X1,X2,X3) != X4 )
            & k3_mcart_1(X4,X5,X6) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
   => ( ? [X6,X5,X4] :
          ( ( k7_mcart_1(sK0,sK1,sK2,sK3) != X6
            | k6_mcart_1(sK0,sK1,sK2,sK3) != X5
            | k5_mcart_1(sK0,sK1,sK2,sK3) != X4 )
          & k3_mcart_1(X4,X5,X6) = sK3 )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X6,X5,X4] :
        ( ( k7_mcart_1(sK0,sK1,sK2,sK3) != X6
          | k6_mcart_1(sK0,sK1,sK2,sK3) != X5
          | k5_mcart_1(sK0,sK1,sK2,sK3) != X4 )
        & k3_mcart_1(X4,X5,X6) = sK3 )
   => ( ( k7_mcart_1(sK0,sK1,sK2,sK3) != sK6
        | k6_mcart_1(sK0,sK1,sK2,sK3) != sK5
        | k5_mcart_1(sK0,sK1,sK2,sK3) != sK4 )
      & sK3 = k3_mcart_1(sK4,sK5,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) != X6
            | k6_mcart_1(X0,X1,X2,X3) != X5
            | k5_mcart_1(X0,X1,X2,X3) != X4 )
          & k3_mcart_1(X4,X5,X6) = X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) != X6
            | k6_mcart_1(X0,X1,X2,X3) != X5
            | k5_mcart_1(X0,X1,X2,X3) != X4 )
          & k3_mcart_1(X4,X5,X6) = X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
       => ~ ( ? [X4,X5,X6] :
                ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                    & k6_mcart_1(X0,X1,X2,X3) = X5
                    & k5_mcart_1(X0,X1,X2,X3) = X4 )
                & k3_mcart_1(X4,X5,X6) = X3 )
            & k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => ~ ( ? [X4,X5,X6] :
              ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                  & k6_mcart_1(X0,X1,X2,X3) = X5
                  & k5_mcart_1(X0,X1,X2,X3) = X4 )
              & k3_mcart_1(X4,X5,X6) = X3 )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).

fof(f65,plain,
    ( spl7_6
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f53,f48,f59])).

fof(f53,plain,
    ( ! [X2,X0,X1] :
        ( k3_mcart_1(X0,X1,X2) != sK3
        | sK4 = X0 )
    | ~ spl7_5 ),
    inference(superposition,[],[f24,f50])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f51,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f18,f48])).

fof(f18,plain,(
    sK3 = k3_mcart_1(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f14,f43])).

fof(f14,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f41,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f17,f38])).

fof(f17,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f15,f28])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:50:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.44  % (9095)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.45  % (9095)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f172,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f31,f36,f41,f46,f51,f65,f78,f87,f105,f111,f116,f121,f129,f136,f152,f163,f171])).
% 0.20/0.46  fof(f171,plain,(
% 0.20/0.46    spl7_8 | ~spl7_11 | ~spl7_14 | ~spl7_16),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f170])).
% 0.20/0.46  fof(f170,plain,(
% 0.20/0.46    $false | (spl7_8 | ~spl7_11 | ~spl7_14 | ~spl7_16)),
% 0.20/0.46    inference(subsumption_resolution,[],[f164,f73])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    k6_mcart_1(sK0,sK1,sK2,sK3) != sK5 | spl7_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f71])).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    spl7_8 <=> k6_mcart_1(sK0,sK1,sK2,sK3) = sK5),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.46  fof(f164,plain,(
% 0.20/0.46    k6_mcart_1(sK0,sK1,sK2,sK3) = sK5 | (~spl7_11 | ~spl7_14 | ~spl7_16)),
% 0.20/0.46    inference(backward_demodulation,[],[f120,f148])).
% 0.20/0.46  fof(f148,plain,(
% 0.20/0.46    sK5 = k2_mcart_1(k1_mcart_1(sK3)) | (~spl7_11 | ~spl7_16)),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f145])).
% 0.20/0.46  fof(f145,plain,(
% 0.20/0.46    sK3 != sK3 | sK5 = k2_mcart_1(k1_mcart_1(sK3)) | (~spl7_11 | ~spl7_16)),
% 0.20/0.46    inference(superposition,[],[f98,f135])).
% 0.20/0.46  fof(f135,plain,(
% 0.20/0.46    sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3)) | ~spl7_16),
% 0.20/0.46    inference(avatar_component_clause,[],[f133])).
% 0.20/0.46  fof(f133,plain,(
% 0.20/0.46    spl7_16 <=> sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) != sK3 | sK5 = X1) ) | ~spl7_11),
% 0.20/0.46    inference(avatar_component_clause,[],[f97])).
% 0.20/0.46  fof(f97,plain,(
% 0.20/0.46    spl7_11 <=> ! [X1,X0,X2] : (k3_mcart_1(X0,X1,X2) != sK3 | sK5 = X1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.46  fof(f120,plain,(
% 0.20/0.46    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) | ~spl7_14),
% 0.20/0.46    inference(avatar_component_clause,[],[f118])).
% 0.20/0.46  fof(f118,plain,(
% 0.20/0.46    spl7_14 <=> k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.20/0.46  fof(f163,plain,(
% 0.20/0.46    spl7_9 | ~spl7_10 | ~spl7_12 | ~spl7_16),
% 0.20/0.46    inference(avatar_split_clause,[],[f155,f133,f108,f84,f75])).
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    spl7_9 <=> k7_mcart_1(sK0,sK1,sK2,sK3) = sK6),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    spl7_10 <=> k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.46  fof(f108,plain,(
% 0.20/0.46    spl7_12 <=> ! [X1,X0,X2] : (k3_mcart_1(X0,X1,X2) != sK3 | sK6 = X2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.46  fof(f155,plain,(
% 0.20/0.46    k7_mcart_1(sK0,sK1,sK2,sK3) = sK6 | (~spl7_10 | ~spl7_12 | ~spl7_16)),
% 0.20/0.46    inference(backward_demodulation,[],[f86,f147])).
% 0.20/0.46  fof(f147,plain,(
% 0.20/0.46    sK6 = k2_mcart_1(sK3) | (~spl7_12 | ~spl7_16)),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f146])).
% 0.20/0.46  fof(f146,plain,(
% 0.20/0.46    sK3 != sK3 | sK6 = k2_mcart_1(sK3) | (~spl7_12 | ~spl7_16)),
% 0.20/0.46    inference(superposition,[],[f109,f135])).
% 0.20/0.46  fof(f109,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) != sK3 | sK6 = X2) ) | ~spl7_12),
% 0.20/0.46    inference(avatar_component_clause,[],[f108])).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) | ~spl7_10),
% 0.20/0.46    inference(avatar_component_clause,[],[f84])).
% 0.20/0.46  fof(f152,plain,(
% 0.20/0.46    ~spl7_6 | spl7_15 | ~spl7_16),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f151])).
% 0.20/0.46  fof(f151,plain,(
% 0.20/0.46    $false | (~spl7_6 | spl7_15 | ~spl7_16)),
% 0.20/0.46    inference(subsumption_resolution,[],[f149,f128])).
% 0.20/0.46  fof(f128,plain,(
% 0.20/0.46    sK4 != k1_mcart_1(k1_mcart_1(sK3)) | spl7_15),
% 0.20/0.46    inference(avatar_component_clause,[],[f126])).
% 0.20/0.46  fof(f126,plain,(
% 0.20/0.46    spl7_15 <=> sK4 = k1_mcart_1(k1_mcart_1(sK3))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.20/0.46  fof(f149,plain,(
% 0.20/0.46    sK4 = k1_mcart_1(k1_mcart_1(sK3)) | (~spl7_6 | ~spl7_16)),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f144])).
% 0.20/0.46  fof(f144,plain,(
% 0.20/0.46    sK3 != sK3 | sK4 = k1_mcart_1(k1_mcart_1(sK3)) | (~spl7_6 | ~spl7_16)),
% 0.20/0.46    inference(superposition,[],[f60,f135])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) != sK3 | sK4 = X0) ) | ~spl7_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f59])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    spl7_6 <=> ! [X1,X0,X2] : (k3_mcart_1(X0,X1,X2) != sK3 | sK4 = X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.46  fof(f136,plain,(
% 0.20/0.46    spl7_16 | spl7_1 | spl7_2 | spl7_3 | ~spl7_4 | ~spl7_10 | ~spl7_13 | ~spl7_14),
% 0.20/0.46    inference(avatar_split_clause,[],[f131,f118,f113,f84,f43,f38,f33,f28,f133])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    spl7_1 <=> k1_xboole_0 = sK0),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    spl7_2 <=> k1_xboole_0 = sK1),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    spl7_3 <=> k1_xboole_0 = sK2),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    spl7_4 <=> m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.46  fof(f113,plain,(
% 0.20/0.46    spl7_13 <=> k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.20/0.46  fof(f131,plain,(
% 0.20/0.46    sK3 = k3_mcart_1(k1_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3)) | (spl7_1 | spl7_2 | spl7_3 | ~spl7_4 | ~spl7_10 | ~spl7_13 | ~spl7_14)),
% 0.20/0.46    inference(forward_demodulation,[],[f130,f115])).
% 0.20/0.46  fof(f115,plain,(
% 0.20/0.46    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) | ~spl7_13),
% 0.20/0.46    inference(avatar_component_clause,[],[f113])).
% 0.20/0.46  fof(f130,plain,(
% 0.20/0.46    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k2_mcart_1(k1_mcart_1(sK3)),k2_mcart_1(sK3)) | (spl7_1 | spl7_2 | spl7_3 | ~spl7_4 | ~spl7_10 | ~spl7_14)),
% 0.20/0.46    inference(forward_demodulation,[],[f104,f120])).
% 0.20/0.46  fof(f104,plain,(
% 0.20/0.46    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k2_mcart_1(sK3)) | (spl7_1 | spl7_2 | spl7_3 | ~spl7_4 | ~spl7_10)),
% 0.20/0.46    inference(forward_demodulation,[],[f103,f86])).
% 0.20/0.46  fof(f103,plain,(
% 0.20/0.46    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | (spl7_1 | spl7_2 | spl7_3 | ~spl7_4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f102,f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    k1_xboole_0 != sK0 | spl7_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f28])).
% 0.20/0.46  fof(f102,plain,(
% 0.20/0.46    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | (spl7_2 | spl7_3 | ~spl7_4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f101,f35])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    k1_xboole_0 != sK1 | spl7_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f33])).
% 0.20/0.46  fof(f101,plain,(
% 0.20/0.46    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl7_3 | ~spl7_4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f100,f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    k1_xboole_0 != sK2 | spl7_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f38])).
% 0.20/0.46  fof(f100,plain,(
% 0.20/0.46    sK3 = k3_mcart_1(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_4),
% 0.20/0.46    inference(resolution,[],[f20,f45])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) | ~spl7_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f43])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).
% 0.20/0.46  fof(f129,plain,(
% 0.20/0.46    ~spl7_15 | spl7_7 | ~spl7_13),
% 0.20/0.46    inference(avatar_split_clause,[],[f124,f113,f67,f126])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    spl7_7 <=> k5_mcart_1(sK0,sK1,sK2,sK3) = sK4),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.46  fof(f124,plain,(
% 0.20/0.46    sK4 != k1_mcart_1(k1_mcart_1(sK3)) | (spl7_7 | ~spl7_13)),
% 0.20/0.46    inference(superposition,[],[f69,f115])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    k5_mcart_1(sK0,sK1,sK2,sK3) != sK4 | spl7_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f67])).
% 0.20/0.46  fof(f121,plain,(
% 0.20/0.46    spl7_14 | spl7_1 | spl7_2 | spl7_3 | ~spl7_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f95,f43,f38,f33,f28,f118])).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) | (spl7_1 | spl7_2 | spl7_3 | ~spl7_4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f94,f30])).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK0 | (spl7_2 | spl7_3 | ~spl7_4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f93,f35])).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl7_3 | ~spl7_4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f92,f40])).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    k6_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_4),
% 0.20/0.46    inference(resolution,[],[f22,f45])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.20/0.46  fof(f116,plain,(
% 0.20/0.46    spl7_13 | spl7_1 | spl7_2 | spl7_3 | ~spl7_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f91,f43,f38,f33,f28,f113])).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) | (spl7_1 | spl7_2 | spl7_3 | ~spl7_4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f90,f30])).
% 0.20/0.46  fof(f90,plain,(
% 0.20/0.46    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK0 | (spl7_2 | spl7_3 | ~spl7_4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f89,f35])).
% 0.20/0.46  fof(f89,plain,(
% 0.20/0.46    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl7_3 | ~spl7_4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f88,f40])).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    k5_mcart_1(sK0,sK1,sK2,sK3) = k1_mcart_1(k1_mcart_1(sK3)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_4),
% 0.20/0.46    inference(resolution,[],[f21,f45])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    spl7_12 | ~spl7_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f63,f48,f108])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    spl7_5 <=> sK3 = k3_mcart_1(sK4,sK5,sK6)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) != sK3 | sK6 = X2) ) | ~spl7_5),
% 0.20/0.46    inference(superposition,[],[f26,f50])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    sK3 = k3_mcart_1(sK4,sK5,sK6) | ~spl7_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f48])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) | X2 = X5) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4,X5] : (k3_mcart_1(X0,X1,X2) = k3_mcart_1(X3,X4,X5) => (X2 = X5 & X1 = X4 & X0 = X3))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).
% 0.20/0.46  fof(f105,plain,(
% 0.20/0.46    spl7_11 | ~spl7_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f56,f48,f97])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) != sK3 | sK5 = X1) ) | ~spl7_5),
% 0.20/0.46    inference(superposition,[],[f25,f50])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) | X1 = X4) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    spl7_10 | spl7_1 | spl7_2 | spl7_3 | ~spl7_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f82,f43,f38,f33,f28,f84])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) | (spl7_1 | spl7_2 | spl7_3 | ~spl7_4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f81,f30])).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) | k1_xboole_0 = sK0 | (spl7_2 | spl7_3 | ~spl7_4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f80,f35])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl7_3 | ~spl7_4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f79,f40])).
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    k7_mcart_1(sK0,sK1,sK2,sK3) = k2_mcart_1(sK3) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_4),
% 0.20/0.46    inference(resolution,[],[f23,f45])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    ~spl7_7 | ~spl7_8 | ~spl7_9),
% 0.20/0.46    inference(avatar_split_clause,[],[f19,f75,f71,f67])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    k7_mcart_1(sK0,sK1,sK2,sK3) != sK6 | k6_mcart_1(sK0,sK1,sK2,sK3) != sK5 | k5_mcart_1(sK0,sK1,sK2,sK3) != sK4),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ((k7_mcart_1(sK0,sK1,sK2,sK3) != sK6 | k6_mcart_1(sK0,sK1,sK2,sK3) != sK5 | k5_mcart_1(sK0,sK1,sK2,sK3) != sK4) & sK3 = k3_mcart_1(sK4,sK5,sK6)) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f7,f12,f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3] : (? [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) != X6 | k6_mcart_1(X0,X1,X2,X3) != X5 | k5_mcart_1(X0,X1,X2,X3) != X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) => (? [X6,X5,X4] : ((k7_mcart_1(sK0,sK1,sK2,sK3) != X6 | k6_mcart_1(sK0,sK1,sK2,sK3) != X5 | k5_mcart_1(sK0,sK1,sK2,sK3) != X4) & k3_mcart_1(X4,X5,X6) = sK3) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ? [X6,X5,X4] : ((k7_mcart_1(sK0,sK1,sK2,sK3) != X6 | k6_mcart_1(sK0,sK1,sK2,sK3) != X5 | k5_mcart_1(sK0,sK1,sK2,sK3) != X4) & k3_mcart_1(X4,X5,X6) = sK3) => ((k7_mcart_1(sK0,sK1,sK2,sK3) != sK6 | k6_mcart_1(sK0,sK1,sK2,sK3) != sK5 | k5_mcart_1(sK0,sK1,sK2,sK3) != sK4) & sK3 = k3_mcart_1(sK4,sK5,sK6))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3] : (? [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) != X6 | k6_mcart_1(X0,X1,X2,X3) != X5 | k5_mcart_1(X0,X1,X2,X3) != X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.46    inference(flattening,[],[f6])).
% 0.20/0.46  fof(f6,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3] : ((? [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) != X6 | k6_mcart_1(X0,X1,X2,X3) != X5 | k5_mcart_1(X0,X1,X2,X3) != X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => ~(? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.20/0.46    inference(negated_conjecture,[],[f4])).
% 0.20/0.46  fof(f4,conjecture,(
% 0.20/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => ~(? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    spl7_6 | ~spl7_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f53,f48,f59])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) != sK3 | sK4 = X0) ) | ~spl7_5),
% 0.20/0.46    inference(superposition,[],[f24,f50])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k3_mcart_1(X0,X1,X2) != k3_mcart_1(X3,X4,X5) | X0 = X3) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    spl7_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f18,f48])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    sK3 = k3_mcart_1(sK4,sK5,sK6)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    spl7_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f14,f43])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ~spl7_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f17,f38])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    k1_xboole_0 != sK2),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ~spl7_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f16,f33])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    k1_xboole_0 != sK1),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ~spl7_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f15,f28])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    k1_xboole_0 != sK0),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (9095)------------------------------
% 0.20/0.46  % (9095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (9095)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (9095)Memory used [KB]: 6268
% 0.20/0.46  % (9095)Time elapsed: 0.061 s
% 0.20/0.46  % (9095)------------------------------
% 0.20/0.46  % (9095)------------------------------
% 0.20/0.46  % (9092)Success in time 0.104 s
%------------------------------------------------------------------------------
