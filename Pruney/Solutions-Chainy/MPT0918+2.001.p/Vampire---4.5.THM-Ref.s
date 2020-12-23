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
% DateTime   : Thu Dec  3 12:59:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 229 expanded)
%              Number of leaves         :   25 ( 107 expanded)
%              Depth                    :    8
%              Number of atoms          :  368 (1038 expanded)
%              Number of equality atoms :  236 ( 802 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f151,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f56,f60,f64,f68,f72,f76,f81,f91,f106,f115,f120,f124,f135,f140,f145,f150])).

fof(f150,plain,
    ( spl9_9
    | spl9_8
    | spl9_7
    | spl9_6
    | ~ spl9_10
    | spl9_4
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f149,f113,f50,f74,f58,f62,f66,f70])).

fof(f70,plain,
    ( spl9_9
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f66,plain,
    ( spl9_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f62,plain,
    ( spl9_7
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f58,plain,
    ( spl9_6
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f74,plain,
    ( spl9_10
  <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f50,plain,
    ( spl9_4
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f113,plain,
    ( spl9_17
  <=> sK8 = k2_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f149,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl9_4
    | ~ spl9_17 ),
    inference(trivial_inequality_removal,[],[f148])).

fof(f148,plain,
    ( sK8 != sK8
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl9_4
    | ~ spl9_17 ),
    inference(forward_demodulation,[],[f147,f114])).

fof(f114,plain,
    ( sK8 = k2_mcart_1(sK4)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f113])).

fof(f147,plain,
    ( sK8 != k2_mcart_1(sK4)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl9_4 ),
    inference(superposition,[],[f51,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f31,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f51,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
    | spl9_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f145,plain,
    ( spl9_9
    | spl9_8
    | spl9_7
    | spl9_6
    | ~ spl9_10
    | spl9_3
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f144,f118,f47,f74,f58,f62,f66,f70])).

fof(f47,plain,
    ( spl9_3
  <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f118,plain,
    ( spl9_18
  <=> sK7 = k2_mcart_1(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f144,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl9_3
    | ~ spl9_18 ),
    inference(trivial_inequality_removal,[],[f143])).

fof(f143,plain,
    ( sK7 != sK7
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl9_3
    | ~ spl9_18 ),
    inference(forward_demodulation,[],[f142,f119])).

fof(f119,plain,
    ( sK7 = k2_mcart_1(k1_mcart_1(sK4))
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f118])).

fof(f142,plain,
    ( sK7 != k2_mcart_1(k1_mcart_1(sK4))
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl9_3 ),
    inference(superposition,[],[f48,f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f30,f33])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
    | spl9_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f140,plain,
    ( spl9_9
    | spl9_8
    | spl9_7
    | spl9_6
    | ~ spl9_10
    | spl9_2
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f138,f122,f44,f74,f58,f62,f66,f70])).

fof(f44,plain,
    ( spl9_2
  <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f122,plain,
    ( spl9_19
  <=> sK6 = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f138,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl9_2
    | ~ spl9_19 ),
    inference(trivial_inequality_removal,[],[f137])).

fof(f137,plain,
    ( sK6 != sK6
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl9_2
    | ~ spl9_19 ),
    inference(forward_demodulation,[],[f136,f123])).

fof(f123,plain,
    ( sK6 = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f122])).

fof(f136,plain,
    ( sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | spl9_2 ),
    inference(superposition,[],[f45,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f29,f33])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
    | spl9_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f135,plain,
    ( spl9_9
    | spl9_8
    | spl9_7
    | spl9_6
    | spl9_1
    | ~ spl9_10
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f129,f104,f74,f41,f58,f62,f66,f70])).

fof(f41,plain,
    ( spl9_1
  <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f104,plain,
    ( spl9_16
  <=> sK5 = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f129,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl9_10
    | ~ spl9_16 ),
    inference(forward_demodulation,[],[f128,f105])).

fof(f105,plain,
    ( sK5 = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f104])).

fof(f128,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl9_10 ),
    inference(resolution,[],[f39,f75])).

fof(f75,plain,
    ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f74])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f28,f33])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f124,plain,
    ( spl9_19
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f111,f89,f122])).

fof(f89,plain,
    ( spl9_13
  <=> k4_tarski(sK5,sK6) = k1_mcart_1(k1_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f111,plain,
    ( sK6 = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | ~ spl9_13 ),
    inference(superposition,[],[f23,f90])).

fof(f90,plain,
    ( k4_tarski(sK5,sK6) = k1_mcart_1(k1_mcart_1(sK4))
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f89])).

fof(f23,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f120,plain,
    ( spl9_18
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f110,f79,f118])).

fof(f79,plain,
    ( spl9_11
  <=> k4_tarski(k4_tarski(sK5,sK6),sK7) = k1_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f110,plain,
    ( sK7 = k2_mcart_1(k1_mcart_1(sK4))
    | ~ spl9_11 ),
    inference(superposition,[],[f23,f80])).

fof(f80,plain,
    ( k4_tarski(k4_tarski(sK5,sK6),sK7) = k1_mcart_1(sK4)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f115,plain,
    ( spl9_17
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f108,f54,f113])).

fof(f54,plain,
    ( spl9_5
  <=> sK4 = k4_tarski(k4_tarski(k4_tarski(sK5,sK6),sK7),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f108,plain,
    ( sK8 = k2_mcart_1(sK4)
    | ~ spl9_5 ),
    inference(superposition,[],[f23,f55])).

fof(f55,plain,
    ( sK4 = k4_tarski(k4_tarski(k4_tarski(sK5,sK6),sK7),sK8)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f106,plain,
    ( spl9_16
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f97,f89,f104])).

fof(f97,plain,
    ( sK5 = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | ~ spl9_13 ),
    inference(superposition,[],[f22,f90])).

fof(f22,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f91,plain,
    ( spl9_13
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f86,f79,f89])).

fof(f86,plain,
    ( k4_tarski(sK5,sK6) = k1_mcart_1(k1_mcart_1(sK4))
    | ~ spl9_11 ),
    inference(superposition,[],[f22,f80])).

fof(f81,plain,
    ( spl9_11
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f77,f54,f79])).

fof(f77,plain,
    ( k4_tarski(k4_tarski(sK5,sK6),sK7) = k1_mcart_1(sK4)
    | ~ spl9_5 ),
    inference(superposition,[],[f22,f55])).

fof(f76,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f35,f74])).

fof(f35,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f15,f33])).

fof(f15,plain,(
    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
      | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
      | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5 )
    & sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f10,f13,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ? [X5,X6,X7,X8] :
            ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
              | k10_mcart_1(X0,X1,X2,X3,X4) != X7
              | k9_mcart_1(X0,X1,X2,X3,X4) != X6
              | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
            & k4_mcart_1(X5,X6,X7,X8) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( ? [X8,X7,X6,X5] :
          ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != X8
            | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != X7
            | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != X6
            | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = sK4 )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X8,X7,X6,X5] :
        ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != X8
          | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != X7
          | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != X6
          | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != X5 )
        & k4_mcart_1(X5,X6,X7,X8) = sK4 )
   => ( ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
        | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
        | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
        | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5 )
      & sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
            | k10_mcart_1(X0,X1,X2,X3,X4) != X7
            | k9_mcart_1(X0,X1,X2,X3,X4) != X6
            | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
            | k10_mcart_1(X0,X1,X2,X3,X4) != X7
            | k9_mcart_1(X0,X1,X2,X3,X4) != X6
            | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
       => ~ ( ? [X5,X6,X7,X8] :
                ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                    & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                    & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                    & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
                & k4_mcart_1(X5,X6,X7,X8) = X4 )
            & k1_xboole_0 != X3
            & k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => ~ ( ? [X5,X6,X7,X8] :
              ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                  & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                  & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                  & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).

fof(f72,plain,(
    ~ spl9_9 ),
    inference(avatar_split_clause,[],[f16,f70])).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
    ~ spl9_8 ),
    inference(avatar_split_clause,[],[f17,f66])).

fof(f17,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,(
    ~ spl9_7 ),
    inference(avatar_split_clause,[],[f18,f62])).

fof(f18,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,(
    ~ spl9_6 ),
    inference(avatar_split_clause,[],[f19,f58])).

fof(f19,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f34,f54])).

fof(f34,plain,(
    sK4 = k4_tarski(k4_tarski(k4_tarski(sK5,sK6),sK7),sK8) ),
    inference(definition_unfolding,[],[f20,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f20,plain,(
    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f21,f50,f47,f44,f41])).

fof(f21,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8
    | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6
    | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:00:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (17795)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.49  % (17803)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.49  % (17795)Refutation not found, incomplete strategy% (17795)------------------------------
% 0.21/0.49  % (17795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (17795)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (17795)Memory used [KB]: 10746
% 0.21/0.49  % (17795)Time elapsed: 0.070 s
% 0.21/0.49  % (17795)------------------------------
% 0.21/0.49  % (17795)------------------------------
% 0.21/0.50  % (17803)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f52,f56,f60,f64,f68,f72,f76,f81,f91,f106,f115,f120,f124,f135,f140,f145,f150])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    spl9_9 | spl9_8 | spl9_7 | spl9_6 | ~spl9_10 | spl9_4 | ~spl9_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f149,f113,f50,f74,f58,f62,f66,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    spl9_9 <=> k1_xboole_0 = sK0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl9_8 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl9_7 <=> k1_xboole_0 = sK2),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    spl9_6 <=> k1_xboole_0 = sK3),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    spl9_10 <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    spl9_4 <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK8),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    spl9_17 <=> sK8 = k2_mcart_1(sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl9_4 | ~spl9_17)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f148])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    sK8 != sK8 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl9_4 | ~spl9_17)),
% 0.21/0.50    inference(forward_demodulation,[],[f147,f114])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    sK8 = k2_mcart_1(sK4) | ~spl9_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f113])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    sK8 != k2_mcart_1(sK4) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl9_4),
% 0.21/0.50    inference(superposition,[],[f51,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(definition_unfolding,[],[f31,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f27,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8 | spl9_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f50])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    spl9_9 | spl9_8 | spl9_7 | spl9_6 | ~spl9_10 | spl9_3 | ~spl9_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f144,f118,f47,f74,f58,f62,f66,f70])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    spl9_3 <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK7),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    spl9_18 <=> sK7 = k2_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl9_3 | ~spl9_18)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f143])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    sK7 != sK7 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl9_3 | ~spl9_18)),
% 0.21/0.50    inference(forward_demodulation,[],[f142,f119])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    sK7 = k2_mcart_1(k1_mcart_1(sK4)) | ~spl9_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f118])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    sK7 != k2_mcart_1(k1_mcart_1(sK4)) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl9_3),
% 0.21/0.50    inference(superposition,[],[f48,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(definition_unfolding,[],[f30,f33])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7 | spl9_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f47])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    spl9_9 | spl9_8 | spl9_7 | spl9_6 | ~spl9_10 | spl9_2 | ~spl9_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f138,f122,f44,f74,f58,f62,f66,f70])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    spl9_2 <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK6),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl9_19 <=> sK6 = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl9_2 | ~spl9_19)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f137])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    sK6 != sK6 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (spl9_2 | ~spl9_19)),
% 0.21/0.50    inference(forward_demodulation,[],[f136,f123])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    sK6 = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | ~spl9_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f122])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    sK6 != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | spl9_2),
% 0.21/0.50    inference(superposition,[],[f45,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(definition_unfolding,[],[f29,f33])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6 | spl9_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f44])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    spl9_9 | spl9_8 | spl9_7 | spl9_6 | spl9_1 | ~spl9_10 | ~spl9_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f129,f104,f74,f41,f58,f62,f66,f70])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    spl9_1 <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl9_16 <=> sK5 = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = sK5 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | (~spl9_10 | ~spl9_16)),
% 0.21/0.50    inference(forward_demodulation,[],[f128,f105])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    sK5 = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | ~spl9_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f104])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl9_10),
% 0.21/0.50    inference(resolution,[],[f39,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | ~spl9_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f74])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(definition_unfolding,[],[f28,f33])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    spl9_19 | ~spl9_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f111,f89,f122])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    spl9_13 <=> k4_tarski(sK5,sK6) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    sK6 = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | ~spl9_13),
% 0.21/0.50    inference(superposition,[],[f23,f90])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    k4_tarski(sK5,sK6) = k1_mcart_1(k1_mcart_1(sK4)) | ~spl9_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f89])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    spl9_18 | ~spl9_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f110,f79,f118])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    spl9_11 <=> k4_tarski(k4_tarski(sK5,sK6),sK7) = k1_mcart_1(sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    sK7 = k2_mcart_1(k1_mcart_1(sK4)) | ~spl9_11),
% 0.21/0.50    inference(superposition,[],[f23,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    k4_tarski(k4_tarski(sK5,sK6),sK7) = k1_mcart_1(sK4) | ~spl9_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f79])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl9_17 | ~spl9_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f108,f54,f113])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    spl9_5 <=> sK4 = k4_tarski(k4_tarski(k4_tarski(sK5,sK6),sK7),sK8)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    sK8 = k2_mcart_1(sK4) | ~spl9_5),
% 0.21/0.50    inference(superposition,[],[f23,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    sK4 = k4_tarski(k4_tarski(k4_tarski(sK5,sK6),sK7),sK8) | ~spl9_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f54])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl9_16 | ~spl9_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f97,f89,f104])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    sK5 = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) | ~spl9_13),
% 0.21/0.50    inference(superposition,[],[f22,f90])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl9_13 | ~spl9_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f86,f79,f89])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    k4_tarski(sK5,sK6) = k1_mcart_1(k1_mcart_1(sK4)) | ~spl9_11),
% 0.21/0.50    inference(superposition,[],[f22,f80])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    spl9_11 | ~spl9_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f77,f54,f79])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    k4_tarski(k4_tarski(sK5,sK6),sK7) = k1_mcart_1(sK4) | ~spl9_5),
% 0.21/0.50    inference(superposition,[],[f22,f55])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl9_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f35,f74])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.21/0.50    inference(definition_unfolding,[],[f15,f33])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ((k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5) & sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f10,f13,f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3,X4] : (? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) => (? [X8,X7,X6,X5] : ((k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != X8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != X7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != X6 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != X5) & k4_mcart_1(X5,X6,X7,X8) = sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X8,X7,X6,X5] : ((k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != X8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != X7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != X6 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != X5) & k4_mcart_1(X5,X6,X7,X8) = sK4) => ((k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5) & sK4 = k4_mcart_1(sK5,sK6,sK7,sK8))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3,X4] : (? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.50    inference(flattening,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3,X4] : ((? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.50    inference(negated_conjecture,[],[f7])).
% 0.21/0.50  fof(f7,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ~spl9_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f16,f70])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    k1_xboole_0 != sK0),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ~spl9_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f17,f66])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    k1_xboole_0 != sK1),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ~spl9_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f18,f62])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    k1_xboole_0 != sK2),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ~spl9_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f19,f58])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    k1_xboole_0 != sK3),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    spl9_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f34,f54])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    sK4 = k4_tarski(k4_tarski(k4_tarski(sK5,sK6),sK7),sK8)),
% 0.21/0.50    inference(definition_unfolding,[],[f20,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f26,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f21,f50,f47,f44,f41])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK8 | k10_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK7 | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK6 | k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != sK5),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (17803)------------------------------
% 0.21/0.50  % (17803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (17803)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (17803)Memory used [KB]: 10874
% 0.21/0.50  % (17803)Time elapsed: 0.076 s
% 0.21/0.50  % (17803)------------------------------
% 0.21/0.50  % (17803)------------------------------
% 0.21/0.50  % (17783)Success in time 0.135 s
%------------------------------------------------------------------------------
