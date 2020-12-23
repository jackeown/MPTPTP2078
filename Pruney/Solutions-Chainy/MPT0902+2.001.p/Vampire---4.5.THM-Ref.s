%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 276 expanded)
%              Number of leaves         :   28 ( 106 expanded)
%              Depth                    :    8
%              Number of atoms          :  407 ( 915 expanded)
%              Number of equality atoms :  232 ( 612 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f556,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f180,f194,f211,f270,f277,f285,f294,f340,f355,f401,f421,f459,f469,f495,f555])).

fof(f555,plain,(
    ~ spl8_29 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f109,f83,f494,f134])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X1,X2),X3) != X0
      | ~ r2_hidden(X2,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X1,X2),X3) != X0
      | ~ r2_hidden(X2,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f67,f113])).

fof(f113,plain,(
    ! [X1] :
      ( sK5(k1_tarski(X1)) = X1
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(resolution,[],[f81,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f81,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f67,plain,(
    ! [X4,X2,X0,X3] :
      ( sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f35,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f35,plain,(
    ! [X4,X2,X0,X3] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | k3_mcart_1(X2,X3,X4) != sK5(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f494,plain,
    ( sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),sK4),k2_mcart_1(sK4))
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f492])).

fof(f492,plain,
    ( spl8_29
  <=> sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),sK4),k2_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f83,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f109,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f42,f41])).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f42,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f495,plain,
    ( spl8_6
    | ~ spl8_10
    | spl8_7
    | spl8_8
    | spl8_9
    | spl8_29
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f490,f161,f95,f492,f177,f173,f169,f184,f165])).

fof(f165,plain,
    ( spl8_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f184,plain,
    ( spl8_10
  <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f169,plain,
    ( spl8_7
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f173,plain,
    ( spl8_8
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f177,plain,
    ( spl8_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f95,plain,
    ( spl8_2
  <=> sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f161,plain,
    ( spl8_5
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f490,plain,
    ( sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),sK4),k2_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK0
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f488,f163])).

fof(f163,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f161])).

fof(f488,plain,
    ( sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK0
    | ~ spl8_2 ),
    inference(superposition,[],[f76,f97])).

fof(f97,plain,
    ( sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4)),k10_mcart_1(X0,X1,X2,X3,X4)),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f61,f55,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

fof(f469,plain,(
    ~ spl8_24 ),
    inference(avatar_contradiction_clause,[],[f460])).

fof(f460,plain,
    ( $false
    | ~ spl8_24 ),
    inference(unit_resulting_resolution,[],[f29,f30,f444,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f444,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f442])).

fof(f442,plain,
    ( spl8_24
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f30,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X4
            | k10_mcart_1(X0,X1,X2,X3,X4) = X4
            | k9_mcart_1(X0,X1,X2,X3,X4) = X4
            | k8_mcart_1(X0,X1,X2,X3,X4) = X4 )
          & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ~ ! [X4] :
                ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
               => ( k11_mcart_1(X0,X1,X2,X3,X4) != X4
                  & k10_mcart_1(X0,X1,X2,X3,X4) != X4
                  & k9_mcart_1(X0,X1,X2,X3,X4) != X4
                  & k8_mcart_1(X0,X1,X2,X3,X4) != X4 ) )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k11_mcart_1(X0,X1,X2,X3,X4) != X4
                & k10_mcart_1(X0,X1,X2,X3,X4) != X4
                & k9_mcart_1(X0,X1,X2,X3,X4) != X4
                & k8_mcart_1(X0,X1,X2,X3,X4) != X4 ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_mcart_1)).

fof(f29,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).

fof(f459,plain,
    ( spl8_24
    | spl8_8
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f430,f418,f173,f442])).

fof(f418,plain,
    ( spl8_21
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f430,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_21 ),
    inference(trivial_inequality_removal,[],[f428])).

fof(f428,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_21 ),
    inference(superposition,[],[f48,f420])).

fof(f420,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f418])).

fof(f421,plain,
    ( spl8_21
    | spl8_7
    | ~ spl8_1
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f414,f161,f91,f169,f418])).

fof(f91,plain,
    ( spl8_1
  <=> sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f414,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl8_1
    | ~ spl8_5 ),
    inference(resolution,[],[f412,f66])).

fof(f66,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f28,f55])).

fof(f28,plain,(
    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f412,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(X1,X0))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X1 )
    | ~ spl8_1
    | ~ spl8_5 ),
    inference(trivial_inequality_removal,[],[f411])).

fof(f411,plain,
    ( ! [X0,X1] :
        ( sK4 != sK4
        | k1_xboole_0 = X0
        | ~ m1_subset_1(sK4,k2_zfmisc_1(X1,X0))
        | k1_xboole_0 = X1 )
    | ~ spl8_1
    | ~ spl8_5 ),
    inference(superposition,[],[f52,f402])).

fof(f402,plain,
    ( sK4 = k2_mcart_1(sK4)
    | ~ spl8_1
    | ~ spl8_5 ),
    inference(superposition,[],[f93,f163])).

fof(f93,plain,
    ( sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X2) != X2
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 )
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => ( k2_mcart_1(X2) != X2
                & k1_mcart_1(X2) != X2 ) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).

fof(f401,plain,(
    ~ spl8_18 ),
    inference(avatar_contradiction_clause,[],[f368])).

fof(f368,plain,
    ( $false
    | ~ spl8_18 ),
    inference(unit_resulting_resolution,[],[f109,f83,f354,f140])).

fof(f140,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) != X0
      | ~ r2_hidden(X2,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) != X0
      | ~ r2_hidden(X2,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f69,f114])).

fof(f114,plain,(
    ! [X2] :
      ( sK6(k1_tarski(X2)) = X2
      | k1_xboole_0 = k1_tarski(X2) ) ),
    inference(resolution,[],[f81,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3] :
      ( sK6(X0) != k4_tarski(k4_tarski(k4_tarski(X2,X3),X4),X5)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f38,f54])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | k4_mcart_1(X2,X3,X4,X5) != sK6(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f354,plain,
    ( sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(sK4))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl8_18
  <=> sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f355,plain,
    ( spl8_6
    | ~ spl8_10
    | spl8_7
    | spl8_8
    | spl8_9
    | spl8_18
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f350,f161,f99,f352,f177,f173,f169,f184,f165])).

fof(f99,plain,
    ( spl8_3
  <=> sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f350,plain,
    ( sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK0
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f348,f163])).

fof(f348,plain,
    ( sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k11_mcart_1(sK0,sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK0
    | ~ spl8_3 ),
    inference(superposition,[],[f76,f101])).

fof(f101,plain,
    ( sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f340,plain,(
    ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f307])).

fof(f307,plain,
    ( $false
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f109,f83,f267,f142])).

fof(f142,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) != X0
      | ~ r2_hidden(X1,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) != X0
      | ~ r2_hidden(X1,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f70,f114])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3] :
      ( sK6(X0) != k4_tarski(k4_tarski(k4_tarski(X2,X3),X4),X5)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f37,f54])).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X2,X0)
      | k4_mcart_1(X2,X3,X4,X5) != sK6(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f267,plain,
    ( sK4 = k4_tarski(k4_tarski(k4_tarski(sK4,k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(sK4))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl8_14
  <=> sK4 = k4_tarski(k4_tarski(k4_tarski(sK4,k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f294,plain,(
    ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f30,f179])).

fof(f179,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f177])).

fof(f285,plain,(
    ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f31,f175])).

fof(f175,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f173])).

fof(f31,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f20])).

fof(f277,plain,(
    ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f32,f171])).

fof(f171,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f169])).

fof(f32,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f20])).

fof(f270,plain,
    ( spl8_6
    | ~ spl8_10
    | spl8_7
    | spl8_8
    | spl8_9
    | spl8_14
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f269,f161,f103,f265,f177,f173,f169,f184,f165])).

fof(f103,plain,
    ( spl8_4
  <=> sK4 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f269,plain,
    ( sK4 = k4_tarski(k4_tarski(k4_tarski(sK4,k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK0
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f229,f105])).

fof(f105,plain,
    ( sK4 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f229,plain,
    ( sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | k1_xboole_0 = sK0
    | ~ spl8_5 ),
    inference(superposition,[],[f76,f163])).

fof(f211,plain,(
    ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f29,f167])).

fof(f167,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f165])).

fof(f194,plain,(
    spl8_10 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl8_10 ),
    inference(subsumption_resolution,[],[f66,f186])).

fof(f186,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f184])).

fof(f180,plain,
    ( spl8_5
    | spl8_6
    | spl8_7
    | spl8_8
    | spl8_9 ),
    inference(avatar_split_clause,[],[f155,f177,f173,f169,f165,f161])).

fof(f155,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) ),
    inference(resolution,[],[f77,f66])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) ) ),
    inference(definition_unfolding,[],[f65,f55])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f106,plain,
    ( spl8_1
    | spl8_2
    | spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f27,f103,f99,f95,f91])).

fof(f27,plain,
    ( sK4 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (7700)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.50  % (7710)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.50  % (7729)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (7704)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (7728)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.51  % (7703)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (7702)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (7713)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (7726)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (7721)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (7718)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (7729)Refutation not found, incomplete strategy% (7729)------------------------------
% 0.20/0.52  % (7729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (7701)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (7729)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (7729)Memory used [KB]: 1663
% 0.20/0.52  % (7729)Time elapsed: 0.114 s
% 0.20/0.52  % (7729)------------------------------
% 0.20/0.52  % (7729)------------------------------
% 0.20/0.52  % (7722)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (7701)Refutation not found, incomplete strategy% (7701)------------------------------
% 0.20/0.53  % (7701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (7701)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (7701)Memory used [KB]: 1791
% 0.20/0.53  % (7701)Time elapsed: 0.126 s
% 0.20/0.53  % (7701)------------------------------
% 0.20/0.53  % (7701)------------------------------
% 0.20/0.53  % (7712)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (7720)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (7712)Refutation not found, incomplete strategy% (7712)------------------------------
% 0.20/0.53  % (7712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (7712)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (7712)Memory used [KB]: 10618
% 0.20/0.53  % (7712)Time elapsed: 0.133 s
% 0.20/0.53  % (7712)------------------------------
% 0.20/0.53  % (7712)------------------------------
% 0.20/0.53  % (7724)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (7723)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (7707)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (7705)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (7724)Refutation not found, incomplete strategy% (7724)------------------------------
% 0.20/0.53  % (7724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (7724)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (7724)Memory used [KB]: 10746
% 0.20/0.53  % (7724)Time elapsed: 0.130 s
% 0.20/0.53  % (7724)------------------------------
% 0.20/0.53  % (7724)------------------------------
% 0.20/0.53  % (7714)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (7714)Refutation not found, incomplete strategy% (7714)------------------------------
% 0.20/0.53  % (7714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (7714)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (7714)Memory used [KB]: 1791
% 0.20/0.53  % (7714)Time elapsed: 0.092 s
% 0.20/0.53  % (7714)------------------------------
% 0.20/0.53  % (7714)------------------------------
% 0.20/0.53  % (7715)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (7726)Refutation not found, incomplete strategy% (7726)------------------------------
% 0.20/0.54  % (7726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (7726)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (7726)Memory used [KB]: 6268
% 0.20/0.54  % (7726)Time elapsed: 0.143 s
% 0.20/0.54  % (7726)------------------------------
% 0.20/0.54  % (7726)------------------------------
% 0.20/0.54  % (7706)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (7725)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (7718)Refutation not found, incomplete strategy% (7718)------------------------------
% 0.20/0.54  % (7718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (7718)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (7718)Memory used [KB]: 1791
% 0.20/0.54  % (7718)Time elapsed: 0.124 s
% 0.20/0.54  % (7718)------------------------------
% 0.20/0.54  % (7718)------------------------------
% 0.20/0.54  % (7708)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (7709)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (7717)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (7727)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (7727)Refutation not found, incomplete strategy% (7727)------------------------------
% 0.20/0.55  % (7727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (7727)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (7727)Memory used [KB]: 6268
% 0.20/0.55  % (7727)Time elapsed: 0.151 s
% 0.20/0.55  % (7727)------------------------------
% 0.20/0.55  % (7727)------------------------------
% 0.20/0.55  % (7717)Refutation not found, incomplete strategy% (7717)------------------------------
% 0.20/0.55  % (7717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (7717)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (7717)Memory used [KB]: 1791
% 0.20/0.55  % (7717)Time elapsed: 0.151 s
% 0.20/0.55  % (7717)------------------------------
% 0.20/0.55  % (7717)------------------------------
% 0.20/0.55  % (7716)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (7719)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (7716)Refutation not found, incomplete strategy% (7716)------------------------------
% 0.20/0.55  % (7716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (7716)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (7716)Memory used [KB]: 10746
% 0.20/0.55  % (7716)Time elapsed: 0.152 s
% 0.20/0.55  % (7716)------------------------------
% 0.20/0.55  % (7716)------------------------------
% 0.20/0.55  % (7711)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.57  % (7713)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f556,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f106,f180,f194,f211,f270,f277,f285,f294,f340,f355,f401,f421,f459,f469,f495,f555])).
% 0.20/0.57  fof(f555,plain,(
% 0.20/0.57    ~spl8_29),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f522])).
% 0.20/0.57  fof(f522,plain,(
% 0.20/0.57    $false | ~spl8_29),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f109,f83,f494,f134])).
% 0.20/0.57  fof(f134,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X1,X2),X3) != X0 | ~r2_hidden(X2,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0)) )),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f133])).
% 0.20/0.57  fof(f133,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X1,X2),X3) != X0 | ~r2_hidden(X2,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0) | k1_xboole_0 = k1_tarski(X0)) )),
% 0.20/0.57    inference(superposition,[],[f67,f113])).
% 0.20/0.57  fof(f113,plain,(
% 0.20/0.57    ( ! [X1] : (sK5(k1_tarski(X1)) = X1 | k1_xboole_0 = k1_tarski(X1)) )),
% 0.20/0.57    inference(resolution,[],[f81,f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f21])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.57    inference(ennf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.20/0.57  fof(f81,plain,(
% 0.20/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 0.20/0.57    inference(equality_resolution,[],[f45])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.57  fof(f67,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X3] : (sK5(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(definition_unfolding,[],[f35,f53])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X3] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | k3_mcart_1(X2,X3,X4) != sK5(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f21])).
% 0.20/0.57  fof(f494,plain,(
% 0.20/0.57    sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),sK4),k2_mcart_1(sK4)) | ~spl8_29),
% 0.20/0.57    inference(avatar_component_clause,[],[f492])).
% 0.20/0.57  fof(f492,plain,(
% 0.20/0.57    spl8_29 <=> sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),sK4),k2_mcart_1(sK4))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.20/0.57  fof(f83,plain,(
% 0.20/0.57    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 0.20/0.57    inference(equality_resolution,[],[f82])).
% 0.20/0.57  fof(f82,plain,(
% 0.20/0.57    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 0.20/0.57    inference(equality_resolution,[],[f44])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f3])).
% 0.20/0.57  fof(f109,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 0.20/0.57    inference(superposition,[],[f42,f41])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f19])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.57    inference(rectify,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.57  fof(f495,plain,(
% 0.20/0.57    spl8_6 | ~spl8_10 | spl8_7 | spl8_8 | spl8_9 | spl8_29 | ~spl8_2 | ~spl8_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f490,f161,f95,f492,f177,f173,f169,f184,f165])).
% 0.20/0.57  fof(f165,plain,(
% 0.20/0.57    spl8_6 <=> k1_xboole_0 = sK0),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.57  fof(f184,plain,(
% 0.20/0.57    spl8_10 <=> m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.57  fof(f169,plain,(
% 0.20/0.57    spl8_7 <=> k1_xboole_0 = sK3),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.57  fof(f173,plain,(
% 0.20/0.57    spl8_8 <=> k1_xboole_0 = sK2),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.57  fof(f177,plain,(
% 0.20/0.57    spl8_9 <=> k1_xboole_0 = sK1),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.57  fof(f95,plain,(
% 0.20/0.57    spl8_2 <=> sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.57  fof(f161,plain,(
% 0.20/0.57    spl8_5 <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.57  fof(f490,plain,(
% 0.20/0.57    sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),sK4),k2_mcart_1(sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK0 | (~spl8_2 | ~spl8_5)),
% 0.20/0.57    inference(forward_demodulation,[],[f488,f163])).
% 0.20/0.57  fof(f163,plain,(
% 0.20/0.57    k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4) | ~spl8_5),
% 0.20/0.57    inference(avatar_component_clause,[],[f161])).
% 0.20/0.57  fof(f488,plain,(
% 0.20/0.57    sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),sK4),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK0 | ~spl8_2),
% 0.20/0.57    inference(superposition,[],[f76,f97])).
% 0.20/0.57  fof(f97,plain,(
% 0.20/0.57    sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) | ~spl8_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f95])).
% 0.20/0.57  fof(f76,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4)),k10_mcart_1(X0,X1,X2,X3,X4)),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(definition_unfolding,[],[f61,f55,f54])).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).
% 0.20/0.57  fof(f61,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4) )),
% 0.20/0.57    inference(cnf_transformation,[],[f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (! [X4] : (k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.57    inference(ennf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).
% 0.20/0.57  fof(f469,plain,(
% 0.20/0.57    ~spl8_24),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f460])).
% 0.20/0.57  fof(f460,plain,(
% 0.20/0.57    $false | ~spl8_24),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f29,f30,f444,f48])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.57  fof(f444,plain,(
% 0.20/0.57    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_24),
% 0.20/0.57    inference(avatar_component_clause,[],[f442])).
% 0.20/0.57  fof(f442,plain,(
% 0.20/0.57    spl8_24 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    k1_xboole_0 != sK1),
% 0.20/0.57    inference(cnf_transformation,[],[f20])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ? [X0,X1,X2,X3] : (? [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X4 | k10_mcart_1(X0,X1,X2,X3,X4) = X4 | k9_mcart_1(X0,X1,X2,X3,X4) = X4 | k8_mcart_1(X0,X1,X2,X3,X4) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.57    inference(ennf_transformation,[],[f18])).
% 0.20/0.57  fof(f18,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) != X4 & k10_mcart_1(X0,X1,X2,X3,X4) != X4 & k9_mcart_1(X0,X1,X2,X3,X4) != X4 & k8_mcart_1(X0,X1,X2,X3,X4) != X4)) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.57    inference(negated_conjecture,[],[f17])).
% 0.20/0.57  fof(f17,conjecture,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) != X4 & k10_mcart_1(X0,X1,X2,X3,X4) != X4 & k9_mcart_1(X0,X1,X2,X3,X4) != X4 & k8_mcart_1(X0,X1,X2,X3,X4) != X4)) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_mcart_1)).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    k1_xboole_0 != sK0),
% 0.20/0.57    inference(cnf_transformation,[],[f20])).
% 0.20/0.57  fof(f459,plain,(
% 0.20/0.57    spl8_24 | spl8_8 | ~spl8_21),
% 0.20/0.57    inference(avatar_split_clause,[],[f430,f418,f173,f442])).
% 0.20/0.57  fof(f418,plain,(
% 0.20/0.57    spl8_21 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.20/0.57  fof(f430,plain,(
% 0.20/0.57    k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_21),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f428])).
% 0.20/0.57  fof(f428,plain,(
% 0.20/0.57    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl8_21),
% 0.20/0.57    inference(superposition,[],[f48,f420])).
% 0.20/0.57  fof(f420,plain,(
% 0.20/0.57    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl8_21),
% 0.20/0.57    inference(avatar_component_clause,[],[f418])).
% 0.20/0.57  fof(f421,plain,(
% 0.20/0.57    spl8_21 | spl8_7 | ~spl8_1 | ~spl8_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f414,f161,f91,f169,f418])).
% 0.20/0.57  fof(f91,plain,(
% 0.20/0.57    spl8_1 <=> sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.57  fof(f414,plain,(
% 0.20/0.57    k1_xboole_0 = sK3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | (~spl8_1 | ~spl8_5)),
% 0.20/0.57    inference(resolution,[],[f412,f66])).
% 0.20/0.57  fof(f66,plain,(
% 0.20/0.57    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.20/0.57    inference(definition_unfolding,[],[f28,f55])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.20/0.57    inference(cnf_transformation,[],[f20])).
% 0.20/0.57  fof(f412,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0 | k1_xboole_0 = X1) ) | (~spl8_1 | ~spl8_5)),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f411])).
% 0.20/0.57  fof(f411,plain,(
% 0.20/0.57    ( ! [X0,X1] : (sK4 != sK4 | k1_xboole_0 = X0 | ~m1_subset_1(sK4,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X1) ) | (~spl8_1 | ~spl8_5)),
% 0.20/0.57    inference(superposition,[],[f52,f402])).
% 0.20/0.57  fof(f402,plain,(
% 0.20/0.57    sK4 = k2_mcart_1(sK4) | (~spl8_1 | ~spl8_5)),
% 0.20/0.57    inference(superposition,[],[f93,f163])).
% 0.20/0.57  fof(f93,plain,(
% 0.20/0.57    sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) | ~spl8_1),
% 0.20/0.57    inference(avatar_component_clause,[],[f91])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k2_mcart_1(X2) != X2 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f24])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ! [X0,X1] : (! [X2] : ((k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2) | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.57    inference(ennf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).
% 0.20/0.57  fof(f401,plain,(
% 0.20/0.57    ~spl8_18),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f368])).
% 0.20/0.57  fof(f368,plain,(
% 0.20/0.57    $false | ~spl8_18),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f109,f83,f354,f140])).
% 0.20/0.57  fof(f140,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) != X0 | ~r2_hidden(X2,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0)) )),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f139])).
% 0.20/0.57  fof(f139,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) != X0 | ~r2_hidden(X2,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0) | k1_xboole_0 = k1_tarski(X0)) )),
% 0.20/0.57    inference(superposition,[],[f69,f114])).
% 0.20/0.57  fof(f114,plain,(
% 0.20/0.57    ( ! [X2] : (sK6(k1_tarski(X2)) = X2 | k1_xboole_0 = k1_tarski(X2)) )),
% 0.20/0.57    inference(resolution,[],[f81,f39])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f22])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.57    inference(ennf_transformation,[],[f12])).
% 0.20/0.57  fof(f12,axiom,(
% 0.20/0.57    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).
% 0.20/0.57  fof(f69,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X5,X3] : (sK6(X0) != k4_tarski(k4_tarski(k4_tarski(X2,X3),X4),X5) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(definition_unfolding,[],[f38,f54])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X5,X3] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | k4_mcart_1(X2,X3,X4,X5) != sK6(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f22])).
% 0.20/0.57  fof(f354,plain,(
% 0.20/0.57    sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) | ~spl8_18),
% 0.20/0.57    inference(avatar_component_clause,[],[f352])).
% 0.20/0.57  fof(f352,plain,(
% 0.20/0.57    spl8_18 <=> sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(sK4))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.20/0.57  fof(f355,plain,(
% 0.20/0.57    spl8_6 | ~spl8_10 | spl8_7 | spl8_8 | spl8_9 | spl8_18 | ~spl8_3 | ~spl8_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f350,f161,f99,f352,f177,f173,f169,f184,f165])).
% 0.20/0.57  fof(f99,plain,(
% 0.20/0.57    spl8_3 <=> sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.57  fof(f350,plain,(
% 0.20/0.57    sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK0 | (~spl8_3 | ~spl8_5)),
% 0.20/0.57    inference(forward_demodulation,[],[f348,f163])).
% 0.20/0.57  fof(f348,plain,(
% 0.20/0.57    sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),sK4),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k11_mcart_1(sK0,sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK0 | ~spl8_3),
% 0.20/0.57    inference(superposition,[],[f76,f101])).
% 0.20/0.57  fof(f101,plain,(
% 0.20/0.57    sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4) | ~spl8_3),
% 0.20/0.57    inference(avatar_component_clause,[],[f99])).
% 0.20/0.57  fof(f340,plain,(
% 0.20/0.57    ~spl8_14),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f307])).
% 0.20/0.57  fof(f307,plain,(
% 0.20/0.57    $false | ~spl8_14),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f109,f83,f267,f142])).
% 0.20/0.57  fof(f142,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) != X0 | ~r2_hidden(X1,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0)) )),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f141])).
% 0.20/0.57  fof(f141,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_tarski(k4_tarski(k4_tarski(X1,X2),X3),X4) != X0 | ~r2_hidden(X1,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0) | k1_xboole_0 = k1_tarski(X0)) )),
% 0.20/0.57    inference(superposition,[],[f70,f114])).
% 0.20/0.57  fof(f70,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X5,X3] : (sK6(X0) != k4_tarski(k4_tarski(k4_tarski(X2,X3),X4),X5) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(definition_unfolding,[],[f37,f54])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X5,X3] : (k1_xboole_0 = X0 | ~r2_hidden(X2,X0) | k4_mcart_1(X2,X3,X4,X5) != sK6(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f22])).
% 0.20/0.57  fof(f267,plain,(
% 0.20/0.57    sK4 = k4_tarski(k4_tarski(k4_tarski(sK4,k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) | ~spl8_14),
% 0.20/0.57    inference(avatar_component_clause,[],[f265])).
% 0.20/0.57  fof(f265,plain,(
% 0.20/0.57    spl8_14 <=> sK4 = k4_tarski(k4_tarski(k4_tarski(sK4,k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(sK4))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.20/0.57  fof(f294,plain,(
% 0.20/0.57    ~spl8_9),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f288])).
% 0.20/0.57  fof(f288,plain,(
% 0.20/0.57    $false | ~spl8_9),
% 0.20/0.57    inference(subsumption_resolution,[],[f30,f179])).
% 0.20/0.57  fof(f179,plain,(
% 0.20/0.57    k1_xboole_0 = sK1 | ~spl8_9),
% 0.20/0.57    inference(avatar_component_clause,[],[f177])).
% 0.20/0.57  fof(f285,plain,(
% 0.20/0.57    ~spl8_8),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f279])).
% 0.20/0.57  fof(f279,plain,(
% 0.20/0.57    $false | ~spl8_8),
% 0.20/0.57    inference(subsumption_resolution,[],[f31,f175])).
% 0.20/0.57  fof(f175,plain,(
% 0.20/0.57    k1_xboole_0 = sK2 | ~spl8_8),
% 0.20/0.57    inference(avatar_component_clause,[],[f173])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    k1_xboole_0 != sK2),
% 0.20/0.57    inference(cnf_transformation,[],[f20])).
% 0.20/0.57  fof(f277,plain,(
% 0.20/0.57    ~spl8_7),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f271])).
% 0.20/0.57  fof(f271,plain,(
% 0.20/0.57    $false | ~spl8_7),
% 0.20/0.57    inference(subsumption_resolution,[],[f32,f171])).
% 0.20/0.57  fof(f171,plain,(
% 0.20/0.57    k1_xboole_0 = sK3 | ~spl8_7),
% 0.20/0.57    inference(avatar_component_clause,[],[f169])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    k1_xboole_0 != sK3),
% 0.20/0.57    inference(cnf_transformation,[],[f20])).
% 0.20/0.57  fof(f270,plain,(
% 0.20/0.57    spl8_6 | ~spl8_10 | spl8_7 | spl8_8 | spl8_9 | spl8_14 | ~spl8_4 | ~spl8_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f269,f161,f103,f265,f177,f173,f169,f184,f165])).
% 0.20/0.57  fof(f103,plain,(
% 0.20/0.57    spl8_4 <=> sK4 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.57  fof(f269,plain,(
% 0.20/0.57    sK4 = k4_tarski(k4_tarski(k4_tarski(sK4,k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK0 | (~spl8_4 | ~spl8_5)),
% 0.20/0.57    inference(forward_demodulation,[],[f229,f105])).
% 0.20/0.57  fof(f105,plain,(
% 0.20/0.57    sK4 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) | ~spl8_4),
% 0.20/0.57    inference(avatar_component_clause,[],[f103])).
% 0.20/0.57  fof(f229,plain,(
% 0.20/0.57    sK4 = k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | k1_xboole_0 = sK0 | ~spl8_5),
% 0.20/0.57    inference(superposition,[],[f76,f163])).
% 0.20/0.57  fof(f211,plain,(
% 0.20/0.57    ~spl8_6),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f206])).
% 0.20/0.57  fof(f206,plain,(
% 0.20/0.57    $false | ~spl8_6),
% 0.20/0.57    inference(subsumption_resolution,[],[f29,f167])).
% 0.20/0.57  fof(f167,plain,(
% 0.20/0.57    k1_xboole_0 = sK0 | ~spl8_6),
% 0.20/0.57    inference(avatar_component_clause,[],[f165])).
% 0.20/0.57  fof(f194,plain,(
% 0.20/0.57    spl8_10),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f193])).
% 0.20/0.57  fof(f193,plain,(
% 0.20/0.57    $false | spl8_10),
% 0.20/0.57    inference(subsumption_resolution,[],[f66,f186])).
% 0.20/0.57  fof(f186,plain,(
% 0.20/0.57    ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | spl8_10),
% 0.20/0.57    inference(avatar_component_clause,[],[f184])).
% 0.20/0.57  fof(f180,plain,(
% 0.20/0.57    spl8_5 | spl8_6 | spl8_7 | spl8_8 | spl8_9),
% 0.20/0.57    inference(avatar_split_clause,[],[f155,f177,f173,f169,f165,f161])).
% 0.20/0.57  fof(f155,plain,(
% 0.20/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | k1_xboole_0 = sK0 | k11_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(sK4)),
% 0.20/0.57    inference(resolution,[],[f77,f66])).
% 0.20/0.57  fof(f77,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f65,f55])).
% 0.20/0.57  fof(f65,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.57    inference(ennf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).
% 0.20/0.57  fof(f106,plain,(
% 0.20/0.57    spl8_1 | spl8_2 | spl8_3 | spl8_4),
% 0.20/0.57    inference(avatar_split_clause,[],[f27,f103,f99,f95,f91])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    sK4 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK4 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK4 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.20/0.57    inference(cnf_transformation,[],[f20])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (7713)------------------------------
% 0.20/0.57  % (7713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (7713)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (7713)Memory used [KB]: 6908
% 0.20/0.57  % (7713)Time elapsed: 0.151 s
% 0.20/0.57  % (7713)------------------------------
% 0.20/0.57  % (7713)------------------------------
% 0.20/0.57  % (7699)Success in time 0.208 s
%------------------------------------------------------------------------------
