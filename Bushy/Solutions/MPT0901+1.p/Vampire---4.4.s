%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t61_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:11 EDT 2019

% Result     : Theorem 30.22s
% Output     : Refutation 30.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 193 expanded)
%              Number of leaves         :   17 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  221 ( 715 expanded)
%              Number of equality atoms :  136 ( 576 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f45856,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f7588,f7629,f7660,f7668,f7677,f7684,f7691,f33509,f45766,f45845])).

fof(f45845,plain,
    ( spl10_5
    | ~ spl10_22 ),
    inference(avatar_contradiction_clause,[],[f45834])).

fof(f45834,plain,
    ( $false
    | ~ spl10_5
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f99,f38793])).

fof(f38793,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | ~ spl10_22 ),
    inference(superposition,[],[f130,f32204])).

fof(f32204,plain,
    ( k1_mcart_1(k1_mcart_1(sK4)) = k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4))
    | ~ spl10_22 ),
    inference(superposition,[],[f129,f7704])).

fof(f7704,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4))
    | ~ spl10_22 ),
    inference(superposition,[],[f129,f7628])).

fof(f7628,plain,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) = sK4
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f7627])).

fof(f7627,plain,
    ( spl10_22
  <=> k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f129,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X5,X1] :
      ( k4_tarski(X1,X2) != k4_tarski(X4,X5)
      | k1_mcart_1(k4_tarski(X1,X2)) = X4 ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X5,X3,X1] :
      ( k4_tarski(X1,X2) != k4_tarski(X4,X5)
      | X3 = X4
      | k1_mcart_1(k4_tarski(X1,X2)) != X3 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_tarski(X1,X2) != X0
      | k4_tarski(X4,X5) != X0
      | X3 = X4
      | k1_mcart_1(X0) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X4
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X4 ) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k1_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t61_mcart_1.p',d1_mcart_1)).

fof(f130,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X5,X1] :
      ( k4_tarski(X1,X2) != k4_tarski(X4,X5)
      | k2_mcart_1(k4_tarski(X1,X2)) = X5 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X5,X3,X1] :
      ( k4_tarski(X1,X2) != k4_tarski(X4,X5)
      | X3 = X5
      | k2_mcart_1(k4_tarski(X1,X2)) != X3 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_tarski(X1,X2) != X0
      | k4_tarski(X4,X5) != X0
      | X3 = X5
      | k2_mcart_1(X0) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X5
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X5 ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k2_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t61_mcart_1.p',d2_mcart_1)).

fof(f99,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl10_5
  <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f45766,plain,
    ( spl10_7
    | ~ spl10_22 ),
    inference(avatar_contradiction_clause,[],[f45755])).

fof(f45755,plain,
    ( $false
    | ~ spl10_7
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f105,f38792])).

fof(f38792,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | ~ spl10_22 ),
    inference(superposition,[],[f129,f32204])).

fof(f105,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl10_7
  <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f33509,plain,
    ( spl10_3
    | ~ spl10_22 ),
    inference(avatar_contradiction_clause,[],[f33501])).

fof(f33501,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f93,f32205])).

fof(f32205,plain,
    ( k2_mcart_1(k1_mcart_1(sK4)) = k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | ~ spl10_22 ),
    inference(superposition,[],[f130,f7704])).

fof(f93,plain,
    ( k2_mcart_1(k1_mcart_1(sK4)) != k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl10_3
  <=> k2_mcart_1(k1_mcart_1(sK4)) != k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f7691,plain,(
    ~ spl10_20 ),
    inference(avatar_contradiction_clause,[],[f7685])).

fof(f7685,plain,
    ( $false
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f48,f7622])).

fof(f7622,plain,
    ( k1_xboole_0 = sK1
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f7621])).

fof(f7621,plain,
    ( spl10_20
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f48,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( k2_mcart_1(X4) != k11_mcart_1(X0,X1,X2,X3,X4)
            | k2_mcart_1(k1_mcart_1(X4)) != k10_mcart_1(X0,X1,X2,X3,X4)
            | k9_mcart_1(X0,X1,X2,X3,X4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            | k8_mcart_1(X0,X1,X2,X3,X4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ~ ! [X4] :
                ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
               => ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
                  & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
                  & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                  & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k2_mcart_1(X4) = k11_mcart_1(X0,X1,X2,X3,X4)
                & k2_mcart_1(k1_mcart_1(X4)) = k10_mcart_1(X0,X1,X2,X3,X4)
                & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t61_mcart_1.p',t61_mcart_1)).

fof(f7684,plain,(
    ~ spl10_18 ),
    inference(avatar_contradiction_clause,[],[f7678])).

fof(f7678,plain,
    ( $false
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f49,f7616])).

fof(f7616,plain,
    ( k1_xboole_0 = sK2
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f7615])).

fof(f7615,plain,
    ( spl10_18
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f49,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f7677,plain,(
    ~ spl10_16 ),
    inference(avatar_contradiction_clause,[],[f7670])).

fof(f7670,plain,
    ( $false
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f50,f7610])).

fof(f7610,plain,
    ( k1_xboole_0 = sK3
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f7609])).

fof(f7609,plain,
    ( spl10_16
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f50,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f30])).

fof(f7668,plain,(
    ~ spl10_12 ),
    inference(avatar_contradiction_clause,[],[f7663])).

fof(f7663,plain,
    ( $false
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f47,f7598])).

fof(f7598,plain,
    ( k1_xboole_0 = sK0
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f7597])).

fof(f7597,plain,
    ( spl10_12
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f47,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f30])).

fof(f7660,plain,(
    spl10_15 ),
    inference(avatar_contradiction_clause,[],[f7657])).

fof(f7657,plain,
    ( $false
    | ~ spl10_15 ),
    inference(subsumption_resolution,[],[f46,f7604])).

fof(f7604,plain,
    ( ~ m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f7603])).

fof(f7603,plain,
    ( spl10_15
  <=> ~ m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f46,plain,(
    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f7629,plain,
    ( spl10_12
    | ~ spl10_15
    | spl10_16
    | spl10_18
    | spl10_20
    | spl10_22
    | ~ spl10_0 ),
    inference(avatar_split_clause,[],[f7589,f83,f7627,f7621,f7615,f7609,f7603,f7597])).

fof(f83,plain,
    ( spl10_0
  <=> k2_mcart_1(sK4) = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f7589,plain,
    ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(sK0,sK1,sK2,sK3,sK4),k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),k2_mcart_1(sK4)) = sK4
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ spl10_0 ),
    inference(superposition,[],[f73,f84])).

fof(f84,plain,
    ( k2_mcart_1(sK4) = k11_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f83])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k4_tarski(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4)),k10_mcart_1(X0,X1,X2,X3,X4)),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f67,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t61_mcart_1.p',d3_mcart_1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t61_mcart_1.p',d4_mcart_1)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => k4_mcart_1(k8_mcart_1(X0,X1,X2,X3,X4),k9_mcart_1(X0,X1,X2,X3,X4),k10_mcart_1(X0,X1,X2,X3,X4),k11_mcart_1(X0,X1,X2,X3,X4)) = X4 )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t61_mcart_1.p',t60_mcart_1)).

fof(f7588,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f7577])).

fof(f7577,plain,
    ( $false
    | ~ spl10_1 ),
    inference(unit_resulting_resolution,[],[f47,f48,f50,f49,f46,f87,f283])).

fof(f283,plain,(
    ! [X47,X45,X48,X46,X49] :
      ( k2_mcart_1(X49) = k11_mcart_1(X45,X46,X47,X48,X49)
      | k1_xboole_0 = X46
      | k1_xboole_0 = X47
      | k1_xboole_0 = X48
      | ~ m1_subset_1(X49,k4_zfmisc_1(X45,X46,X47,X48))
      | k1_xboole_0 = X45 ) ),
    inference(superposition,[],[f130,f73])).

fof(f87,plain,
    ( k2_mcart_1(sK4) != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl10_1
  <=> k2_mcart_1(sK4) != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f106,plain,
    ( ~ spl10_1
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f45,f104,f98,f92,f86])).

fof(f45,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK4) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k9_mcart_1(sK0,sK1,sK2,sK3,sK4) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK4)))
    | k2_mcart_1(k1_mcart_1(sK4)) != k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | k2_mcart_1(sK4) != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
