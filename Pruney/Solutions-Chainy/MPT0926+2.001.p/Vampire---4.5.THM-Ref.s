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
% DateTime   : Thu Dec  3 12:59:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 297 expanded)
%              Number of leaves         :   27 ( 130 expanded)
%              Depth                    :   10
%              Number of atoms          :  523 (1406 expanded)
%              Number of equality atoms :  268 ( 927 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f184,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f36,f41,f46,f51,f56,f61,f66,f72,f77,f122,f144,f146,f151,f156,f157,f164,f169,f174,f175,f182,f183])).

fof(f183,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) != k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f182,plain,
    ( spl10_22
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f109,f74,f63,f58,f53,f48,f179])).

fof(f179,plain,
    ( spl10_22
  <=> k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f48,plain,
    ( spl10_6
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f53,plain,
    ( spl10_7
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f58,plain,
    ( spl10_8
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f63,plain,
    ( spl10_9
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f74,plain,
    ( spl10_11
  <=> m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f109,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f108,f50])).

fof(f50,plain,
    ( k1_xboole_0 != sK4
    | spl10_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f108,plain,
    ( k1_xboole_0 = sK4
    | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | spl10_7
    | spl10_8
    | spl10_9
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f107,f65])).

fof(f65,plain,
    ( k1_xboole_0 != sK7
    | spl10_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f107,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | spl10_7
    | spl10_8
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f106,f60])).

fof(f60,plain,
    ( k1_xboole_0 != sK6
    | spl10_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f106,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | spl10_7
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f99,f55])).

fof(f55,plain,
    ( k1_xboole_0 != sK5
    | spl10_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f99,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_11 ),
    inference(resolution,[],[f76,f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
            & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
            & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
                & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f76,plain,
    ( m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f175,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f174,plain,
    ( spl10_21
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f105,f74,f63,f58,f53,f48,f171])).

fof(f171,plain,
    ( spl10_21
  <=> k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f105,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f104,f50])).

fof(f104,plain,
    ( k1_xboole_0 = sK4
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | spl10_7
    | spl10_8
    | spl10_9
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f103,f65])).

fof(f103,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | spl10_7
    | spl10_8
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f102,f60])).

fof(f102,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | spl10_7
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f98,f55])).

fof(f98,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_11 ),
    inference(resolution,[],[f76,f18])).

fof(f18,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f169,plain,
    ( spl10_20
    | spl10_2
    | spl10_3
    | spl10_4
    | spl10_5
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f89,f69,f43,f38,f33,f28,f166])).

fof(f166,plain,
    ( spl10_20
  <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f28,plain,
    ( spl10_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f33,plain,
    ( spl10_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f38,plain,
    ( spl10_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f43,plain,
    ( spl10_5
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f69,plain,
    ( spl10_10
  <=> m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f89,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | spl10_2
    | spl10_3
    | spl10_4
    | spl10_5
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f88,f30])).

fof(f30,plain,
    ( k1_xboole_0 != sK0
    | spl10_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f88,plain,
    ( k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | spl10_3
    | spl10_4
    | spl10_5
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f87,f45])).

fof(f45,plain,
    ( k1_xboole_0 != sK3
    | spl10_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f87,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | spl10_3
    | spl10_4
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f86,f40])).

fof(f40,plain,
    ( k1_xboole_0 != sK2
    | spl10_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f86,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | spl10_3
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f79,f35])).

fof(f35,plain,
    ( k1_xboole_0 != sK1
    | spl10_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f79,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl10_10 ),
    inference(resolution,[],[f71,f19])).

fof(f71,plain,
    ( m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f164,plain,
    ( spl10_19
    | spl10_2
    | spl10_3
    | spl10_4
    | spl10_5
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f85,f69,f43,f38,f33,f28,f161])).

fof(f161,plain,
    ( spl10_19
  <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f85,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | spl10_2
    | spl10_3
    | spl10_4
    | spl10_5
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f84,f30])).

fof(f84,plain,
    ( k1_xboole_0 = sK0
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | spl10_3
    | spl10_4
    | spl10_5
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f83,f45])).

fof(f83,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | spl10_3
    | spl10_4
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f82,f40])).

fof(f82,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | spl10_3
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f78,f35])).

fof(f78,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | ~ spl10_10 ),
    inference(resolution,[],[f71,f18])).

fof(f157,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k2_mcart_1(k1_mcart_1(sK8))
    | k2_mcart_1(k1_mcart_1(sK8)) != k10_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f156,plain,
    ( spl10_18
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f113,f74,f63,f58,f53,f48,f153])).

fof(f153,plain,
    ( spl10_18
  <=> k2_mcart_1(k1_mcart_1(sK8)) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f113,plain,
    ( k2_mcart_1(k1_mcart_1(sK8)) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f112,f50])).

fof(f112,plain,
    ( k1_xboole_0 = sK4
    | k2_mcart_1(k1_mcart_1(sK8)) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | spl10_7
    | spl10_8
    | spl10_9
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f111,f65])).

fof(f111,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k2_mcart_1(k1_mcart_1(sK8)) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | spl10_7
    | spl10_8
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f110,f60])).

fof(f110,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k2_mcart_1(k1_mcart_1(sK8)) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | spl10_7
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f100,f55])).

fof(f100,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k2_mcart_1(k1_mcart_1(sK8)) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_11 ),
    inference(resolution,[],[f76,f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f151,plain,
    ( spl10_17
    | spl10_2
    | spl10_3
    | spl10_4
    | spl10_5
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f93,f69,f43,f38,f33,f28,f148])).

fof(f148,plain,
    ( spl10_17
  <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f93,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | spl10_2
    | spl10_3
    | spl10_4
    | spl10_5
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f92,f30])).

fof(f92,plain,
    ( k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | spl10_3
    | spl10_4
    | spl10_5
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f91,f45])).

fof(f91,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | spl10_3
    | spl10_4
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f90,f40])).

fof(f90,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | spl10_3
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f80,f35])).

fof(f80,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | ~ spl10_10 ),
    inference(resolution,[],[f71,f20])).

fof(f146,plain,
    ( spl10_6
    | spl10_7
    | spl10_8
    | spl10_9
    | ~ spl10_11
    | spl10_16 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9
    | ~ spl10_11
    | spl10_16 ),
    inference(subsumption_resolution,[],[f117,f143])).

fof(f143,plain,
    ( k2_mcart_1(sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | spl10_16 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl10_16
  <=> k2_mcart_1(sK8) = k11_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f117,plain,
    ( k2_mcart_1(sK8) = k11_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | spl10_6
    | spl10_7
    | spl10_8
    | spl10_9
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f116,f50])).

fof(f116,plain,
    ( k1_xboole_0 = sK4
    | k2_mcart_1(sK8) = k11_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | spl10_7
    | spl10_8
    | spl10_9
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f115,f65])).

fof(f115,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k2_mcart_1(sK8) = k11_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | spl10_7
    | spl10_8
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f114,f60])).

fof(f114,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k2_mcart_1(sK8) = k11_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | spl10_7
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f101,f55])).

fof(f101,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK4
    | k2_mcart_1(sK8) = k11_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_11 ),
    inference(resolution,[],[f76,f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f144,plain,
    ( ~ spl10_13
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_16
    | ~ spl10_1
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f127,f119,f23,f141,f137,f133,f129])).

fof(f129,plain,
    ( spl10_13
  <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f133,plain,
    ( spl10_14
  <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f137,plain,
    ( spl10_15
  <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f23,plain,
    ( spl10_1
  <=> sK8 = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f119,plain,
    ( spl10_12
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f127,plain,
    ( k2_mcart_1(sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_1
    | ~ spl10_12 ),
    inference(forward_demodulation,[],[f126,f121])).

fof(f121,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f126,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | ~ spl10_1 ),
    inference(forward_demodulation,[],[f125,f25])).

fof(f25,plain,
    ( sK8 = sK9
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f125,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | ~ spl10_1 ),
    inference(forward_demodulation,[],[f124,f25])).

fof(f124,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | ~ spl10_1 ),
    inference(forward_demodulation,[],[f123,f25])).

fof(f123,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8)
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | ~ spl10_1 ),
    inference(forward_demodulation,[],[f6,f25])).

fof(f6,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK9)
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ? [X8] :
          ( ? [X9] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X8) != k11_mcart_1(X4,X5,X6,X7,X9)
                | k10_mcart_1(X0,X1,X2,X3,X8) != k10_mcart_1(X4,X5,X6,X7,X9)
                | k9_mcart_1(X0,X1,X2,X3,X8) != k9_mcart_1(X4,X5,X6,X7,X9)
                | k8_mcart_1(X0,X1,X2,X3,X8) != k8_mcart_1(X4,X5,X6,X7,X9) )
              & X8 = X9
              & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
          & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
      & k1_xboole_0 != X7
      & k1_xboole_0 != X6
      & k1_xboole_0 != X5
      & k1_xboole_0 != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ~ ( ? [X8] :
              ( ? [X9] :
                  ( ~ ( k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9)
                      & k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9)
                      & k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9)
                      & k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9) )
                  & X8 = X9
                  & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
              & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
          & k1_xboole_0 != X7
          & k1_xboole_0 != X6
          & k1_xboole_0 != X5
          & k1_xboole_0 != X4
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ~ ( ? [X8] :
            ( ? [X9] :
                ( ~ ( k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9)
                    & k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9)
                    & k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9)
                    & k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9) )
                & X8 = X9
                & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7)) )
            & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X7
        & k1_xboole_0 != X6
        & k1_xboole_0 != X5
        & k1_xboole_0 != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_mcart_1)).

fof(f122,plain,
    ( spl10_12
    | spl10_2
    | spl10_3
    | spl10_4
    | spl10_5
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f97,f69,f43,f38,f33,f28,f119])).

fof(f97,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | spl10_2
    | spl10_3
    | spl10_4
    | spl10_5
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f96,f30])).

fof(f96,plain,
    ( k1_xboole_0 = sK0
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | spl10_3
    | spl10_4
    | spl10_5
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f95,f45])).

fof(f95,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | spl10_3
    | spl10_4
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f94,f40])).

fof(f94,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | spl10_3
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f81,f35])).

fof(f81,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | ~ spl10_10 ),
    inference(resolution,[],[f71,f21])).

fof(f77,plain,
    ( spl10_11
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f67,f23,f74])).

fof(f67,plain,
    ( m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    | ~ spl10_1 ),
    inference(forward_demodulation,[],[f7,f25])).

fof(f7,plain,(
    m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f4])).

fof(f72,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f9,f69])).

fof(f9,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f66,plain,(
    ~ spl10_9 ),
    inference(avatar_split_clause,[],[f17,f63])).

fof(f17,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f4])).

fof(f61,plain,(
    ~ spl10_8 ),
    inference(avatar_split_clause,[],[f16,f58])).

fof(f16,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f4])).

fof(f56,plain,(
    ~ spl10_7 ),
    inference(avatar_split_clause,[],[f15,f53])).

fof(f15,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f4])).

fof(f51,plain,(
    ~ spl10_6 ),
    inference(avatar_split_clause,[],[f14,f48])).

fof(f14,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f4])).

fof(f46,plain,(
    ~ spl10_5 ),
    inference(avatar_split_clause,[],[f13,f43])).

fof(f13,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f4])).

fof(f41,plain,(
    ~ spl10_4 ),
    inference(avatar_split_clause,[],[f12,f38])).

fof(f12,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f4])).

fof(f36,plain,(
    ~ spl10_3 ),
    inference(avatar_split_clause,[],[f11,f33])).

fof(f11,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f4])).

fof(f31,plain,(
    ~ spl10_2 ),
    inference(avatar_split_clause,[],[f10,f28])).

fof(f10,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f4])).

fof(f26,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f8,f23])).

fof(f8,plain,(
    sK8 = sK9 ),
    inference(cnf_transformation,[],[f4])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:52:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.44  % (16132)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.44  % (16132)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f184,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f26,f31,f36,f41,f46,f51,f56,f61,f66,f72,f77,f122,f144,f146,f151,f156,f157,f164,f169,f174,f175,f182,f183])).
% 0.20/0.44  fof(f183,plain,(
% 0.20/0.44    k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) != k9_mcart_1(sK4,sK5,sK6,sK7,sK8) | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8)),
% 0.20/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.44  fof(f182,plain,(
% 0.20/0.44    spl10_22 | spl10_6 | spl10_7 | spl10_8 | spl10_9 | ~spl10_11),
% 0.20/0.44    inference(avatar_split_clause,[],[f109,f74,f63,f58,f53,f48,f179])).
% 0.20/0.44  fof(f179,plain,(
% 0.20/0.44    spl10_22 <=> k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 0.20/0.44  fof(f48,plain,(
% 0.20/0.44    spl10_6 <=> k1_xboole_0 = sK4),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.20/0.44  fof(f53,plain,(
% 0.20/0.44    spl10_7 <=> k1_xboole_0 = sK5),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    spl10_8 <=> k1_xboole_0 = sK6),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.20/0.44  fof(f63,plain,(
% 0.20/0.44    spl10_9 <=> k1_xboole_0 = sK7),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.20/0.44  fof(f74,plain,(
% 0.20/0.44    spl10_11 <=> m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.20/0.44  fof(f109,plain,(
% 0.20/0.44    k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8) | (spl10_6 | spl10_7 | spl10_8 | spl10_9 | ~spl10_11)),
% 0.20/0.44    inference(subsumption_resolution,[],[f108,f50])).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    k1_xboole_0 != sK4 | spl10_6),
% 0.20/0.44    inference(avatar_component_clause,[],[f48])).
% 0.20/0.44  fof(f108,plain,(
% 0.20/0.44    k1_xboole_0 = sK4 | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8) | (spl10_7 | spl10_8 | spl10_9 | ~spl10_11)),
% 0.20/0.44    inference(subsumption_resolution,[],[f107,f65])).
% 0.20/0.44  fof(f65,plain,(
% 0.20/0.44    k1_xboole_0 != sK7 | spl10_9),
% 0.20/0.44    inference(avatar_component_clause,[],[f63])).
% 0.20/0.44  fof(f107,plain,(
% 0.20/0.44    k1_xboole_0 = sK7 | k1_xboole_0 = sK4 | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8) | (spl10_7 | spl10_8 | ~spl10_11)),
% 0.20/0.44    inference(subsumption_resolution,[],[f106,f60])).
% 0.20/0.44  fof(f60,plain,(
% 0.20/0.44    k1_xboole_0 != sK6 | spl10_8),
% 0.20/0.44    inference(avatar_component_clause,[],[f58])).
% 0.20/0.44  fof(f106,plain,(
% 0.20/0.44    k1_xboole_0 = sK6 | k1_xboole_0 = sK7 | k1_xboole_0 = sK4 | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8) | (spl10_7 | ~spl10_11)),
% 0.20/0.44    inference(subsumption_resolution,[],[f99,f55])).
% 0.20/0.44  fof(f55,plain,(
% 0.20/0.44    k1_xboole_0 != sK5 | spl10_7),
% 0.20/0.44    inference(avatar_component_clause,[],[f53])).
% 0.20/0.44  fof(f99,plain,(
% 0.20/0.44    k1_xboole_0 = sK5 | k1_xboole_0 = sK6 | k1_xboole_0 = sK7 | k1_xboole_0 = sK4 | k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8) | ~spl10_11),
% 0.20/0.44    inference(resolution,[],[f76,f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,plain,(
% 0.20/0.44    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.44    inference(ennf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).
% 0.20/0.44  fof(f76,plain,(
% 0.20/0.44    m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) | ~spl10_11),
% 0.20/0.44    inference(avatar_component_clause,[],[f74])).
% 0.20/0.44  fof(f175,plain,(
% 0.20/0.44    k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8) | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8)),
% 0.20/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.44  fof(f174,plain,(
% 0.20/0.44    spl10_21 | spl10_6 | spl10_7 | spl10_8 | spl10_9 | ~spl10_11),
% 0.20/0.44    inference(avatar_split_clause,[],[f105,f74,f63,f58,f53,f48,f171])).
% 0.20/0.44  fof(f171,plain,(
% 0.20/0.44    spl10_21 <=> k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.20/0.44  fof(f105,plain,(
% 0.20/0.44    k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8) | (spl10_6 | spl10_7 | spl10_8 | spl10_9 | ~spl10_11)),
% 0.20/0.44    inference(subsumption_resolution,[],[f104,f50])).
% 0.20/0.44  fof(f104,plain,(
% 0.20/0.44    k1_xboole_0 = sK4 | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8) | (spl10_7 | spl10_8 | spl10_9 | ~spl10_11)),
% 0.20/0.44    inference(subsumption_resolution,[],[f103,f65])).
% 0.20/0.44  fof(f103,plain,(
% 0.20/0.44    k1_xboole_0 = sK7 | k1_xboole_0 = sK4 | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8) | (spl10_7 | spl10_8 | ~spl10_11)),
% 0.20/0.44    inference(subsumption_resolution,[],[f102,f60])).
% 0.20/0.44  fof(f102,plain,(
% 0.20/0.44    k1_xboole_0 = sK6 | k1_xboole_0 = sK7 | k1_xboole_0 = sK4 | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8) | (spl10_7 | ~spl10_11)),
% 0.20/0.44    inference(subsumption_resolution,[],[f98,f55])).
% 0.20/0.44  fof(f98,plain,(
% 0.20/0.44    k1_xboole_0 = sK5 | k1_xboole_0 = sK6 | k1_xboole_0 = sK7 | k1_xboole_0 = sK4 | k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8) | ~spl10_11),
% 0.20/0.44    inference(resolution,[],[f76,f18])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f169,plain,(
% 0.20/0.44    spl10_20 | spl10_2 | spl10_3 | spl10_4 | spl10_5 | ~spl10_10),
% 0.20/0.44    inference(avatar_split_clause,[],[f89,f69,f43,f38,f33,f28,f166])).
% 0.20/0.44  fof(f166,plain,(
% 0.20/0.44    spl10_20 <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    spl10_2 <=> k1_xboole_0 = sK0),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    spl10_3 <=> k1_xboole_0 = sK1),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    spl10_4 <=> k1_xboole_0 = sK2),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    spl10_5 <=> k1_xboole_0 = sK3),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.20/0.44  fof(f69,plain,(
% 0.20/0.44    spl10_10 <=> m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.20/0.44  fof(f89,plain,(
% 0.20/0.44    k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | (spl10_2 | spl10_3 | spl10_4 | spl10_5 | ~spl10_10)),
% 0.20/0.44    inference(subsumption_resolution,[],[f88,f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    k1_xboole_0 != sK0 | spl10_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f28])).
% 0.20/0.44  fof(f88,plain,(
% 0.20/0.44    k1_xboole_0 = sK0 | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | (spl10_3 | spl10_4 | spl10_5 | ~spl10_10)),
% 0.20/0.44    inference(subsumption_resolution,[],[f87,f45])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    k1_xboole_0 != sK3 | spl10_5),
% 0.20/0.44    inference(avatar_component_clause,[],[f43])).
% 0.20/0.44  fof(f87,plain,(
% 0.20/0.44    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | (spl10_3 | spl10_4 | ~spl10_10)),
% 0.20/0.44    inference(subsumption_resolution,[],[f86,f40])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    k1_xboole_0 != sK2 | spl10_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f38])).
% 0.20/0.44  fof(f86,plain,(
% 0.20/0.44    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | (spl10_3 | ~spl10_10)),
% 0.20/0.44    inference(subsumption_resolution,[],[f79,f35])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    k1_xboole_0 != sK1 | spl10_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f33])).
% 0.20/0.44  fof(f79,plain,(
% 0.20/0.44    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | ~spl10_10),
% 0.20/0.44    inference(resolution,[],[f71,f19])).
% 0.20/0.44  fof(f71,plain,(
% 0.20/0.44    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | ~spl10_10),
% 0.20/0.44    inference(avatar_component_clause,[],[f69])).
% 0.20/0.44  fof(f164,plain,(
% 0.20/0.44    spl10_19 | spl10_2 | spl10_3 | spl10_4 | spl10_5 | ~spl10_10),
% 0.20/0.44    inference(avatar_split_clause,[],[f85,f69,f43,f38,f33,f28,f161])).
% 0.20/0.44  fof(f161,plain,(
% 0.20/0.44    spl10_19 <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.20/0.44  fof(f85,plain,(
% 0.20/0.44    k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | (spl10_2 | spl10_3 | spl10_4 | spl10_5 | ~spl10_10)),
% 0.20/0.44    inference(subsumption_resolution,[],[f84,f30])).
% 0.20/0.44  fof(f84,plain,(
% 0.20/0.44    k1_xboole_0 = sK0 | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | (spl10_3 | spl10_4 | spl10_5 | ~spl10_10)),
% 0.20/0.44    inference(subsumption_resolution,[],[f83,f45])).
% 0.20/0.44  fof(f83,plain,(
% 0.20/0.44    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | (spl10_3 | spl10_4 | ~spl10_10)),
% 0.20/0.44    inference(subsumption_resolution,[],[f82,f40])).
% 0.20/0.44  fof(f82,plain,(
% 0.20/0.44    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | (spl10_3 | ~spl10_10)),
% 0.20/0.44    inference(subsumption_resolution,[],[f78,f35])).
% 0.20/0.44  fof(f78,plain,(
% 0.20/0.44    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | ~spl10_10),
% 0.20/0.44    inference(resolution,[],[f71,f18])).
% 0.20/0.44  fof(f157,plain,(
% 0.20/0.44    k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k2_mcart_1(k1_mcart_1(sK8)) | k2_mcart_1(k1_mcart_1(sK8)) != k10_mcart_1(sK4,sK5,sK6,sK7,sK8) | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8)),
% 0.20/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.44  fof(f156,plain,(
% 0.20/0.44    spl10_18 | spl10_6 | spl10_7 | spl10_8 | spl10_9 | ~spl10_11),
% 0.20/0.44    inference(avatar_split_clause,[],[f113,f74,f63,f58,f53,f48,f153])).
% 0.20/0.44  fof(f153,plain,(
% 0.20/0.44    spl10_18 <=> k2_mcart_1(k1_mcart_1(sK8)) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.20/0.44  fof(f113,plain,(
% 0.20/0.44    k2_mcart_1(k1_mcart_1(sK8)) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8) | (spl10_6 | spl10_7 | spl10_8 | spl10_9 | ~spl10_11)),
% 0.20/0.44    inference(subsumption_resolution,[],[f112,f50])).
% 0.20/0.44  fof(f112,plain,(
% 0.20/0.44    k1_xboole_0 = sK4 | k2_mcart_1(k1_mcart_1(sK8)) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8) | (spl10_7 | spl10_8 | spl10_9 | ~spl10_11)),
% 0.20/0.44    inference(subsumption_resolution,[],[f111,f65])).
% 0.20/0.44  fof(f111,plain,(
% 0.20/0.44    k1_xboole_0 = sK7 | k1_xboole_0 = sK4 | k2_mcart_1(k1_mcart_1(sK8)) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8) | (spl10_7 | spl10_8 | ~spl10_11)),
% 0.20/0.44    inference(subsumption_resolution,[],[f110,f60])).
% 0.20/0.44  fof(f110,plain,(
% 0.20/0.44    k1_xboole_0 = sK6 | k1_xboole_0 = sK7 | k1_xboole_0 = sK4 | k2_mcart_1(k1_mcart_1(sK8)) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8) | (spl10_7 | ~spl10_11)),
% 0.20/0.44    inference(subsumption_resolution,[],[f100,f55])).
% 0.20/0.44  fof(f100,plain,(
% 0.20/0.44    k1_xboole_0 = sK5 | k1_xboole_0 = sK6 | k1_xboole_0 = sK7 | k1_xboole_0 = sK4 | k2_mcart_1(k1_mcart_1(sK8)) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8) | ~spl10_11),
% 0.20/0.44    inference(resolution,[],[f76,f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f151,plain,(
% 0.20/0.44    spl10_17 | spl10_2 | spl10_3 | spl10_4 | spl10_5 | ~spl10_10),
% 0.20/0.44    inference(avatar_split_clause,[],[f93,f69,f43,f38,f33,f28,f148])).
% 0.20/0.44  fof(f148,plain,(
% 0.20/0.44    spl10_17 <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.20/0.44  fof(f93,plain,(
% 0.20/0.44    k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) | (spl10_2 | spl10_3 | spl10_4 | spl10_5 | ~spl10_10)),
% 0.20/0.44    inference(subsumption_resolution,[],[f92,f30])).
% 0.20/0.44  fof(f92,plain,(
% 0.20/0.44    k1_xboole_0 = sK0 | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) | (spl10_3 | spl10_4 | spl10_5 | ~spl10_10)),
% 0.20/0.44    inference(subsumption_resolution,[],[f91,f45])).
% 0.20/0.44  fof(f91,plain,(
% 0.20/0.44    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) | (spl10_3 | spl10_4 | ~spl10_10)),
% 0.20/0.44    inference(subsumption_resolution,[],[f90,f40])).
% 0.20/0.44  fof(f90,plain,(
% 0.20/0.44    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) | (spl10_3 | ~spl10_10)),
% 0.20/0.44    inference(subsumption_resolution,[],[f80,f35])).
% 0.20/0.44  fof(f80,plain,(
% 0.20/0.44    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) | ~spl10_10),
% 0.20/0.44    inference(resolution,[],[f71,f20])).
% 0.20/0.44  fof(f146,plain,(
% 0.20/0.44    spl10_6 | spl10_7 | spl10_8 | spl10_9 | ~spl10_11 | spl10_16),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f145])).
% 0.20/0.44  fof(f145,plain,(
% 0.20/0.44    $false | (spl10_6 | spl10_7 | spl10_8 | spl10_9 | ~spl10_11 | spl10_16)),
% 0.20/0.44    inference(subsumption_resolution,[],[f117,f143])).
% 0.20/0.44  fof(f143,plain,(
% 0.20/0.44    k2_mcart_1(sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK8) | spl10_16),
% 0.20/0.44    inference(avatar_component_clause,[],[f141])).
% 0.20/0.44  fof(f141,plain,(
% 0.20/0.44    spl10_16 <=> k2_mcart_1(sK8) = k11_mcart_1(sK4,sK5,sK6,sK7,sK8)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.20/0.44  fof(f117,plain,(
% 0.20/0.44    k2_mcart_1(sK8) = k11_mcart_1(sK4,sK5,sK6,sK7,sK8) | (spl10_6 | spl10_7 | spl10_8 | spl10_9 | ~spl10_11)),
% 0.20/0.44    inference(subsumption_resolution,[],[f116,f50])).
% 0.20/0.44  fof(f116,plain,(
% 0.20/0.44    k1_xboole_0 = sK4 | k2_mcart_1(sK8) = k11_mcart_1(sK4,sK5,sK6,sK7,sK8) | (spl10_7 | spl10_8 | spl10_9 | ~spl10_11)),
% 0.20/0.44    inference(subsumption_resolution,[],[f115,f65])).
% 0.20/0.44  fof(f115,plain,(
% 0.20/0.44    k1_xboole_0 = sK7 | k1_xboole_0 = sK4 | k2_mcart_1(sK8) = k11_mcart_1(sK4,sK5,sK6,sK7,sK8) | (spl10_7 | spl10_8 | ~spl10_11)),
% 0.20/0.44    inference(subsumption_resolution,[],[f114,f60])).
% 0.20/0.44  fof(f114,plain,(
% 0.20/0.44    k1_xboole_0 = sK6 | k1_xboole_0 = sK7 | k1_xboole_0 = sK4 | k2_mcart_1(sK8) = k11_mcart_1(sK4,sK5,sK6,sK7,sK8) | (spl10_7 | ~spl10_11)),
% 0.20/0.44    inference(subsumption_resolution,[],[f101,f55])).
% 0.20/0.44  fof(f101,plain,(
% 0.20/0.44    k1_xboole_0 = sK5 | k1_xboole_0 = sK6 | k1_xboole_0 = sK7 | k1_xboole_0 = sK4 | k2_mcart_1(sK8) = k11_mcart_1(sK4,sK5,sK6,sK7,sK8) | ~spl10_11),
% 0.20/0.44    inference(resolution,[],[f76,f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f144,plain,(
% 0.20/0.44    ~spl10_13 | ~spl10_14 | ~spl10_15 | ~spl10_16 | ~spl10_1 | ~spl10_12),
% 0.20/0.44    inference(avatar_split_clause,[],[f127,f119,f23,f141,f137,f133,f129])).
% 0.20/0.44  fof(f129,plain,(
% 0.20/0.44    spl10_13 <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k8_mcart_1(sK4,sK5,sK6,sK7,sK8)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.20/0.44  fof(f133,plain,(
% 0.20/0.44    spl10_14 <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k9_mcart_1(sK4,sK5,sK6,sK7,sK8)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.20/0.44  fof(f137,plain,(
% 0.20/0.44    spl10_15 <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k10_mcart_1(sK4,sK5,sK6,sK7,sK8)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    spl10_1 <=> sK8 = sK9),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.44  fof(f119,plain,(
% 0.20/0.44    spl10_12 <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.20/0.44  fof(f127,plain,(
% 0.20/0.44    k2_mcart_1(sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK8) | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK8) | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK8) | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8) | (~spl10_1 | ~spl10_12)),
% 0.20/0.44    inference(forward_demodulation,[],[f126,f121])).
% 0.20/0.44  fof(f121,plain,(
% 0.20/0.44    k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) | ~spl10_12),
% 0.20/0.44    inference(avatar_component_clause,[],[f119])).
% 0.20/0.44  fof(f126,plain,(
% 0.20/0.44    k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK8) | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK8) | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK8) | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8) | ~spl10_1),
% 0.20/0.44    inference(forward_demodulation,[],[f125,f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    sK8 = sK9 | ~spl10_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f23])).
% 0.20/0.44  fof(f125,plain,(
% 0.20/0.44    k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK8) | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK8) | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8) | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9) | ~spl10_1),
% 0.20/0.44    inference(forward_demodulation,[],[f124,f25])).
% 0.20/0.44  fof(f124,plain,(
% 0.20/0.44    k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK8) | k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8) | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK9) | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9) | ~spl10_1),
% 0.20/0.44    inference(forward_demodulation,[],[f123,f25])).
% 0.20/0.44  fof(f123,plain,(
% 0.20/0.44    k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK8) | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK9) | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK9) | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9) | ~spl10_1),
% 0.20/0.44    inference(forward_demodulation,[],[f6,f25])).
% 0.20/0.44  fof(f6,plain,(
% 0.20/0.44    k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k8_mcart_1(sK4,sK5,sK6,sK7,sK9) | k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k9_mcart_1(sK4,sK5,sK6,sK7,sK9) | k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k10_mcart_1(sK4,sK5,sK6,sK7,sK9) | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k11_mcart_1(sK4,sK5,sK6,sK7,sK9)),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,plain,(
% 0.20/0.44    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (? [X8] : (? [X9] : ((k11_mcart_1(X0,X1,X2,X3,X8) != k11_mcart_1(X4,X5,X6,X7,X9) | k10_mcart_1(X0,X1,X2,X3,X8) != k10_mcart_1(X4,X5,X6,X7,X9) | k9_mcart_1(X0,X1,X2,X3,X8) != k9_mcart_1(X4,X5,X6,X7,X9) | k8_mcart_1(X0,X1,X2,X3,X8) != k8_mcart_1(X4,X5,X6,X7,X9)) & X8 = X9 & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X7 & k1_xboole_0 != X6 & k1_xboole_0 != X5 & k1_xboole_0 != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.44    inference(ennf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : ~(? [X8] : (? [X9] : (~(k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9) & k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9) & k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9) & k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9)) & X8 = X9 & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X7 & k1_xboole_0 != X6 & k1_xboole_0 != X5 & k1_xboole_0 != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.44    inference(negated_conjecture,[],[f2])).
% 0.20/0.44  fof(f2,conjecture,(
% 0.20/0.44    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ~(? [X8] : (? [X9] : (~(k11_mcart_1(X0,X1,X2,X3,X8) = k11_mcart_1(X4,X5,X6,X7,X9) & k10_mcart_1(X0,X1,X2,X3,X8) = k10_mcart_1(X4,X5,X6,X7,X9) & k9_mcart_1(X0,X1,X2,X3,X8) = k9_mcart_1(X4,X5,X6,X7,X9) & k8_mcart_1(X0,X1,X2,X3,X8) = k8_mcart_1(X4,X5,X6,X7,X9)) & X8 = X9 & m1_subset_1(X9,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X7 & k1_xboole_0 != X6 & k1_xboole_0 != X5 & k1_xboole_0 != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_mcart_1)).
% 0.20/0.44  fof(f122,plain,(
% 0.20/0.44    spl10_12 | spl10_2 | spl10_3 | spl10_4 | spl10_5 | ~spl10_10),
% 0.20/0.44    inference(avatar_split_clause,[],[f97,f69,f43,f38,f33,f28,f119])).
% 0.20/0.44  fof(f97,plain,(
% 0.20/0.44    k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) | (spl10_2 | spl10_3 | spl10_4 | spl10_5 | ~spl10_10)),
% 0.20/0.44    inference(subsumption_resolution,[],[f96,f30])).
% 0.20/0.44  fof(f96,plain,(
% 0.20/0.44    k1_xboole_0 = sK0 | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) | (spl10_3 | spl10_4 | spl10_5 | ~spl10_10)),
% 0.20/0.44    inference(subsumption_resolution,[],[f95,f45])).
% 0.20/0.44  fof(f95,plain,(
% 0.20/0.44    k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) | (spl10_3 | spl10_4 | ~spl10_10)),
% 0.20/0.44    inference(subsumption_resolution,[],[f94,f40])).
% 0.20/0.44  fof(f94,plain,(
% 0.20/0.44    k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) | (spl10_3 | ~spl10_10)),
% 0.20/0.44    inference(subsumption_resolution,[],[f81,f35])).
% 0.20/0.44  fof(f81,plain,(
% 0.20/0.44    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) | ~spl10_10),
% 0.20/0.44    inference(resolution,[],[f71,f21])).
% 0.20/0.44  fof(f77,plain,(
% 0.20/0.44    spl10_11 | ~spl10_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f67,f23,f74])).
% 0.20/0.44  fof(f67,plain,(
% 0.20/0.44    m1_subset_1(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) | ~spl10_1),
% 0.20/0.44    inference(forward_demodulation,[],[f7,f25])).
% 0.20/0.44  fof(f7,plain,(
% 0.20/0.44    m1_subset_1(sK9,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f72,plain,(
% 0.20/0.44    spl10_10),
% 0.20/0.44    inference(avatar_split_clause,[],[f9,f69])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f66,plain,(
% 0.20/0.44    ~spl10_9),
% 0.20/0.44    inference(avatar_split_clause,[],[f17,f63])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    k1_xboole_0 != sK7),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f61,plain,(
% 0.20/0.44    ~spl10_8),
% 0.20/0.44    inference(avatar_split_clause,[],[f16,f58])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    k1_xboole_0 != sK6),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f56,plain,(
% 0.20/0.44    ~spl10_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f15,f53])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    k1_xboole_0 != sK5),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    ~spl10_6),
% 0.20/0.44    inference(avatar_split_clause,[],[f14,f48])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    k1_xboole_0 != sK4),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f46,plain,(
% 0.20/0.44    ~spl10_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f13,f43])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    k1_xboole_0 != sK3),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    ~spl10_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f12,f38])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    k1_xboole_0 != sK2),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    ~spl10_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f11,f33])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    k1_xboole_0 != sK1),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ~spl10_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f10,f28])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    k1_xboole_0 != sK0),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    spl10_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f8,f23])).
% 0.20/0.44  fof(f8,plain,(
% 0.20/0.44    sK8 = sK9),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (16132)------------------------------
% 0.20/0.44  % (16132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (16132)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (16132)Memory used [KB]: 10746
% 0.20/0.44  % (16132)Time elapsed: 0.048 s
% 0.20/0.44  % (16132)------------------------------
% 0.20/0.44  % (16132)------------------------------
% 0.20/0.44  % (16128)Success in time 0.088 s
%------------------------------------------------------------------------------
