%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:09 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 302 expanded)
%              Number of leaves         :   27 ( 105 expanded)
%              Depth                    :   13
%              Number of atoms          :  348 ( 778 expanded)
%              Number of equality atoms :  165 ( 440 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1036,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f234,f343,f698,f733,f771,f812,f830,f860,f873,f963,f992,f1024,f1028,f1033])).

fof(f1033,plain,(
    ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f1030])).

fof(f1030,plain,
    ( $false
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f25,f690])).

fof(f690,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f688])).

fof(f688,plain,
    ( spl6_17
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f25,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X3
            | k6_mcart_1(X0,X1,X2,X3) = X3
            | k5_mcart_1(X0,X1,X2,X3) = X3 )
          & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ! [X3] :
                ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
               => ( k7_mcart_1(X0,X1,X2,X3) != X3
                  & k6_mcart_1(X0,X1,X2,X3) != X3
                  & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).

fof(f1028,plain,(
    ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f1025])).

fof(f1025,plain,
    ( $false
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f26,f686])).

fof(f686,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f684])).

fof(f684,plain,
    ( spl6_16
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f26,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f1024,plain,
    ( spl6_23
    | ~ spl6_29 ),
    inference(avatar_contradiction_clause,[],[f1001])).

fof(f1001,plain,
    ( $false
    | spl6_23
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f806,f495,f991,f452])).

fof(f452,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X1,X2),X3) != X0
      | ~ r2_hidden(X1,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(duplicate_literal_removal,[],[f447])).

fof(f447,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(X1,X2),X3) != X0
      | ~ r2_hidden(X1,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f59,f444])).

fof(f444,plain,(
    ! [X0] :
      ( sK4(k1_tarski(X0)) = X0
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(resolution,[],[f443,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f443,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X2))
      | X1 = X2 ) ),
    inference(condensation,[],[f442])).

fof(f442,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f441,f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f47,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f441,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_enumset1(X0,X0,X1))
      | ~ r2_hidden(X1,k1_tarski(X2)) ) ),
    inference(trivial_inequality_removal,[],[f440])).

fof(f440,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X1) != k1_enumset1(X0,X0,X1)
      | ~ r2_hidden(X1,k1_tarski(X2))
      | r2_hidden(X2,k1_enumset1(X0,X0,X1)) ) ),
    inference(superposition,[],[f67,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X1) != k4_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f51,f32,f32])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f59,plain,(
    ! [X4,X2,X0,X3] :
      ( sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f29,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f29,plain,(
    ! [X4,X2,X0,X3] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X2,X0)
      | k3_mcart_1(X2,X3,X4) != sK4(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f991,plain,
    ( sK3 = k4_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f989])).

fof(f989,plain,
    ( spl6_29
  <=> sK3 = k4_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f495,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(condensation,[],[f491])).

fof(f491,plain,(
    ! [X8,X9] :
      ( r2_hidden(X8,k1_tarski(X9))
      | r2_hidden(X9,k1_tarski(X9)) ) ),
    inference(resolution,[],[f487,f80])).

fof(f80,plain,(
    ! [X3,X1] : r2_hidden(X3,k1_enumset1(X3,X3,X1)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k1_enumset1(X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f48,f32])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f487,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X8,k1_enumset1(X6,X6,X7))
      | r2_hidden(X7,k1_tarski(X8))
      | r2_hidden(X6,k1_tarski(X8)) ) ),
    inference(trivial_inequality_removal,[],[f486])).

fof(f486,plain,(
    ! [X6,X8,X7] :
      ( k1_enumset1(X6,X6,X7) != k1_enumset1(X6,X6,X7)
      | ~ r2_hidden(X8,k1_enumset1(X6,X6,X7))
      | r2_hidden(X7,k1_tarski(X8))
      | r2_hidden(X6,k1_tarski(X8)) ) ),
    inference(superposition,[],[f39,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X1) = k4_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f52,f32,f32])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X1,X2)
      | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f806,plain,
    ( k1_xboole_0 != k1_tarski(sK3)
    | spl6_23 ),
    inference(avatar_component_clause,[],[f805])).

fof(f805,plain,
    ( spl6_23
  <=> k1_xboole_0 = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f992,plain,
    ( spl6_14
    | ~ spl6_15
    | spl6_16
    | spl6_17
    | spl6_29
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f986,f91,f989,f688,f684,f680,f676])).

fof(f676,plain,
    ( spl6_14
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f680,plain,
    ( spl6_15
  <=> m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f91,plain,
    ( spl6_3
  <=> sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f986,plain,
    ( sK3 = k4_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0
    | ~ spl6_3 ),
    inference(superposition,[],[f69,f93])).

fof(f93,plain,
    ( sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f53,f41,f40])).

fof(f41,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(f963,plain,(
    ~ spl6_27 ),
    inference(avatar_contradiction_clause,[],[f938])).

fof(f938,plain,
    ( $false
    | ~ spl6_27 ),
    inference(unit_resulting_resolution,[],[f95,f872])).

fof(f872,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f870])).

fof(f870,plain,
    ( spl6_27
  <=> sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f95,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X2 ),
    inference(forward_demodulation,[],[f73,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f73,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | k2_mcart_1(X0) != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f873,plain,
    ( spl6_14
    | ~ spl6_15
    | spl6_16
    | spl6_17
    | spl6_27
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f862,f83,f870,f688,f684,f680,f676])).

fof(f83,plain,
    ( spl6_1
  <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f862,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0
    | ~ spl6_1 ),
    inference(superposition,[],[f69,f85])).

fof(f85,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f860,plain,
    ( ~ spl6_4
    | ~ spl6_23 ),
    inference(avatar_contradiction_clause,[],[f857])).

fof(f857,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_23 ),
    inference(unit_resulting_resolution,[],[f218,f840])).

fof(f840,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl6_23 ),
    inference(superposition,[],[f495,f807])).

fof(f807,plain,
    ( k1_xboole_0 = k1_tarski(sK3)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f805])).

fof(f218,plain,
    ( ! [X3] : ~ r2_hidden(X3,k1_xboole_0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl6_4
  <=> ! [X3] : ~ r2_hidden(X3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f830,plain,(
    spl6_24 ),
    inference(avatar_contradiction_clause,[],[f822])).

fof(f822,plain,
    ( $false
    | spl6_24 ),
    inference(unit_resulting_resolution,[],[f811,f80,f811,f487])).

fof(f811,plain,
    ( ~ r2_hidden(sK3,k1_tarski(sK3))
    | spl6_24 ),
    inference(avatar_component_clause,[],[f809])).

fof(f809,plain,
    ( spl6_24
  <=> r2_hidden(sK3,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f812,plain,
    ( spl6_23
    | ~ spl6_24
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f778,f768,f809,f805])).

fof(f768,plain,
    ( spl6_20
  <=> sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f778,plain,
    ( ~ r2_hidden(sK3,k1_tarski(sK3))
    | k1_xboole_0 = k1_tarski(sK3)
    | ~ spl6_20 ),
    inference(superposition,[],[f482,f770])).

fof(f770,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f768])).

fof(f482,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(k4_tarski(k4_tarski(X1,X0),X2)))
      | k1_xboole_0 = k1_tarski(k4_tarski(k4_tarski(X1,X0),X2)) ) ),
    inference(equality_resolution,[],[f451])).

fof(f451,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(k4_tarski(X5,X6),X7) != X4
      | ~ r2_hidden(X6,k1_tarski(X4))
      | k1_xboole_0 = k1_tarski(X4) ) ),
    inference(duplicate_literal_removal,[],[f448])).

fof(f448,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(k4_tarski(X5,X6),X7) != X4
      | ~ r2_hidden(X6,k1_tarski(X4))
      | k1_xboole_0 = k1_tarski(X4)
      | k1_xboole_0 = k1_tarski(X4) ) ),
    inference(superposition,[],[f58,f444])).

fof(f58,plain,(
    ! [X4,X2,X0,X3] :
      ( sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f30,f40])).

% (19221)Refutation not found, incomplete strategy% (19221)------------------------------
% (19221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19221)Termination reason: Refutation not found, incomplete strategy

% (19221)Memory used [KB]: 2046
% (19221)Time elapsed: 0.225 s
% (19221)------------------------------
% (19221)------------------------------
fof(f30,plain,(
    ! [X4,X2,X0,X3] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | k3_mcart_1(X2,X3,X4) != sK4(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f771,plain,
    ( spl6_14
    | ~ spl6_15
    | spl6_16
    | spl6_17
    | spl6_20
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f742,f87,f768,f688,f684,f680,f676])).

fof(f87,plain,
    ( spl6_2
  <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f742,plain,
    ( sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK0
    | ~ spl6_2 ),
    inference(superposition,[],[f69,f89])).

fof(f89,plain,
    ( sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f733,plain,(
    ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f731])).

fof(f731,plain,
    ( $false
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f24,f678])).

fof(f678,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f676])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).

fof(f698,plain,(
    spl6_15 ),
    inference(avatar_contradiction_clause,[],[f697])).

fof(f697,plain,
    ( $false
    | spl6_15 ),
    inference(subsumption_resolution,[],[f57,f682])).

fof(f682,plain,
    ( ~ m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f680])).

fof(f57,plain,(
    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f23,f41])).

fof(f23,plain,(
    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f343,plain,(
    ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f96,f282])).

fof(f282,plain,
    ( ! [X0,X1] : X0 = X1
    | ~ spl6_8 ),
    inference(condensation,[],[f268])).

fof(f268,plain,
    ( ! [X0,X3,X1] :
        ( X1 = X3
        | X0 = X3 )
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f81,f233])).

fof(f233,plain,
    ( ! [X8,X7] : r2_hidden(X7,X8)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl6_8
  <=> ! [X7,X8] : r2_hidden(X7,X8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f96,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X1 ),
    inference(forward_demodulation,[],[f74,f33])).

fof(f33,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | k1_mcart_1(X0) != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f234,plain,
    ( spl6_4
    | spl6_8 ),
    inference(avatar_split_clause,[],[f211,f232,f217])).

fof(f211,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(X7,X8)
      | ~ r2_hidden(X6,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(X7,X8)
      | ~ r2_hidden(X6,k1_xboole_0)
      | ~ r2_hidden(X6,k1_xboole_0) ) ),
    inference(superposition,[],[f109,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( k2_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(condensation,[],[f135])).

fof(f135,plain,(
    ! [X19,X20,X18] :
      ( k2_mcart_1(X19) = X18
      | k2_mcart_1(X19) = X20
      | ~ r2_hidden(X19,k1_xboole_0) ) ),
    inference(resolution,[],[f81,f109])).

fof(f109,plain,(
    ! [X2,X3] :
      ( r2_hidden(k2_mcart_1(X3),X2)
      | ~ r2_hidden(X3,k1_xboole_0) ) ),
    inference(superposition,[],[f43,f76])).

fof(f76,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f94,plain,
    ( spl6_1
    | spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f22,f91,f87,f83])).

fof(f22,plain,
    ( sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)
    | sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:03:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.52  % (19237)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.23/0.52  % (19220)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.23/0.52  % (19245)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.23/0.52  % (19231)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.52  % (19221)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.23/0.52  % (19230)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.23/0.53  % (19238)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.23/0.53  % (19229)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.23/0.53  % (19225)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.53  % (19234)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.23/0.53  % (19237)Refutation not found, incomplete strategy% (19237)------------------------------
% 0.23/0.53  % (19237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (19237)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (19237)Memory used [KB]: 1791
% 0.23/0.53  % (19237)Time elapsed: 0.111 s
% 0.23/0.53  % (19237)------------------------------
% 0.23/0.53  % (19237)------------------------------
% 0.23/0.53  % (19234)Refutation not found, incomplete strategy% (19234)------------------------------
% 0.23/0.53  % (19234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (19234)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (19234)Memory used [KB]: 1791
% 0.23/0.53  % (19234)Time elapsed: 0.122 s
% 0.23/0.53  % (19234)------------------------------
% 0.23/0.53  % (19234)------------------------------
% 0.23/0.54  % (19244)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.23/0.54  % (19224)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.23/0.54  % (19239)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.23/0.54  % (19222)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.23/0.54  % (19249)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.23/0.54  % (19232)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.23/0.54  % (19226)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.54  % (19240)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.23/0.54  % (19223)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.54  % (19246)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.23/0.54  % (19236)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.23/0.54  % (19246)Refutation not found, incomplete strategy% (19246)------------------------------
% 0.23/0.54  % (19246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (19242)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.23/0.55  % (19247)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.23/0.55  % (19241)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.23/0.55  % (19232)Refutation not found, incomplete strategy% (19232)------------------------------
% 0.23/0.55  % (19232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (19232)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (19232)Memory used [KB]: 10746
% 0.23/0.55  % (19232)Time elapsed: 0.144 s
% 0.23/0.55  % (19232)------------------------------
% 0.23/0.55  % (19232)------------------------------
% 0.23/0.55  % (19249)Refutation not found, incomplete strategy% (19249)------------------------------
% 0.23/0.55  % (19249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (19249)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (19249)Memory used [KB]: 1663
% 0.23/0.55  % (19249)Time elapsed: 0.003 s
% 0.23/0.55  % (19249)------------------------------
% 0.23/0.55  % (19249)------------------------------
% 0.23/0.55  % (19246)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (19246)Memory used [KB]: 6268
% 0.23/0.55  % (19246)Time elapsed: 0.132 s
% 0.23/0.55  % (19246)------------------------------
% 0.23/0.55  % (19246)------------------------------
% 0.23/0.55  % (19230)Refutation not found, incomplete strategy% (19230)------------------------------
% 0.23/0.55  % (19230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (19233)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.23/0.56  % (19243)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.23/0.56  % (19228)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.56  % (19248)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.23/0.56  % (19235)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.23/0.56  % (19236)Refutation not found, incomplete strategy% (19236)------------------------------
% 0.23/0.56  % (19236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (19236)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (19236)Memory used [KB]: 10618
% 0.23/0.56  % (19236)Time elapsed: 0.152 s
% 0.23/0.56  % (19236)------------------------------
% 0.23/0.56  % (19236)------------------------------
% 0.23/0.57  % (19227)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.23/0.57  % (19230)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (19230)Memory used [KB]: 11001
% 0.23/0.57  % (19230)Time elapsed: 0.142 s
% 0.23/0.57  % (19230)------------------------------
% 0.23/0.57  % (19230)------------------------------
% 0.23/0.58  % (19248)Refutation not found, incomplete strategy% (19248)------------------------------
% 0.23/0.58  % (19248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.58  % (19248)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.58  
% 0.23/0.58  % (19248)Memory used [KB]: 11001
% 0.23/0.58  % (19248)Time elapsed: 0.158 s
% 0.23/0.58  % (19248)------------------------------
% 0.23/0.58  % (19248)------------------------------
% 1.94/0.64  % (19233)Refutation found. Thanks to Tanya!
% 1.94/0.64  % SZS status Theorem for theBenchmark
% 1.94/0.64  % SZS output start Proof for theBenchmark
% 1.94/0.64  fof(f1036,plain,(
% 1.94/0.64    $false),
% 1.94/0.64    inference(avatar_sat_refutation,[],[f94,f234,f343,f698,f733,f771,f812,f830,f860,f873,f963,f992,f1024,f1028,f1033])).
% 1.94/0.64  fof(f1033,plain,(
% 1.94/0.64    ~spl6_17),
% 1.94/0.64    inference(avatar_contradiction_clause,[],[f1030])).
% 1.94/0.64  fof(f1030,plain,(
% 1.94/0.64    $false | ~spl6_17),
% 1.94/0.64    inference(subsumption_resolution,[],[f25,f690])).
% 1.94/0.64  fof(f690,plain,(
% 1.94/0.64    k1_xboole_0 = sK1 | ~spl6_17),
% 1.94/0.64    inference(avatar_component_clause,[],[f688])).
% 1.94/0.64  fof(f688,plain,(
% 1.94/0.64    spl6_17 <=> k1_xboole_0 = sK1),
% 1.94/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.94/0.64  fof(f25,plain,(
% 1.94/0.64    k1_xboole_0 != sK1),
% 1.94/0.64    inference(cnf_transformation,[],[f16])).
% 1.94/0.64  fof(f16,plain,(
% 1.94/0.64    ? [X0,X1,X2] : (? [X3] : ((k7_mcart_1(X0,X1,X2,X3) = X3 | k6_mcart_1(X0,X1,X2,X3) = X3 | k5_mcart_1(X0,X1,X2,X3) = X3) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.94/0.64    inference(ennf_transformation,[],[f15])).
% 1.94/0.64  fof(f15,negated_conjecture,(
% 1.94/0.64    ~! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.94/0.64    inference(negated_conjecture,[],[f14])).
% 1.94/0.64  fof(f14,conjecture,(
% 1.94/0.64    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.94/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).
% 1.94/0.64  fof(f1028,plain,(
% 1.94/0.64    ~spl6_16),
% 1.94/0.64    inference(avatar_contradiction_clause,[],[f1025])).
% 1.94/0.64  fof(f1025,plain,(
% 1.94/0.64    $false | ~spl6_16),
% 1.94/0.64    inference(subsumption_resolution,[],[f26,f686])).
% 1.94/0.64  fof(f686,plain,(
% 1.94/0.64    k1_xboole_0 = sK2 | ~spl6_16),
% 1.94/0.64    inference(avatar_component_clause,[],[f684])).
% 1.94/0.64  fof(f684,plain,(
% 1.94/0.64    spl6_16 <=> k1_xboole_0 = sK2),
% 1.94/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.94/0.64  fof(f26,plain,(
% 1.94/0.64    k1_xboole_0 != sK2),
% 1.94/0.64    inference(cnf_transformation,[],[f16])).
% 1.94/0.64  fof(f1024,plain,(
% 1.94/0.64    spl6_23 | ~spl6_29),
% 1.94/0.64    inference(avatar_contradiction_clause,[],[f1001])).
% 1.94/0.64  fof(f1001,plain,(
% 1.94/0.64    $false | (spl6_23 | ~spl6_29)),
% 1.94/0.64    inference(unit_resulting_resolution,[],[f806,f495,f991,f452])).
% 1.94/0.64  fof(f452,plain,(
% 1.94/0.64    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X1,X2),X3) != X0 | ~r2_hidden(X1,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0)) )),
% 1.94/0.64    inference(duplicate_literal_removal,[],[f447])).
% 1.94/0.64  fof(f447,plain,(
% 1.94/0.64    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(X1,X2),X3) != X0 | ~r2_hidden(X1,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0) | k1_xboole_0 = k1_tarski(X0)) )),
% 1.94/0.64    inference(superposition,[],[f59,f444])).
% 1.94/0.64  fof(f444,plain,(
% 1.94/0.64    ( ! [X0] : (sK4(k1_tarski(X0)) = X0 | k1_xboole_0 = k1_tarski(X0)) )),
% 1.94/0.64    inference(resolution,[],[f443,f31])).
% 1.94/0.64  fof(f31,plain,(
% 1.94/0.64    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.94/0.64    inference(cnf_transformation,[],[f18])).
% 1.94/0.64  fof(f18,plain,(
% 1.94/0.64    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.94/0.64    inference(ennf_transformation,[],[f10])).
% 1.94/0.64  fof(f10,axiom,(
% 1.94/0.64    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.94/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 1.94/0.64  fof(f443,plain,(
% 1.94/0.64    ( ! [X2,X1] : (~r2_hidden(X1,k1_tarski(X2)) | X1 = X2) )),
% 1.94/0.64    inference(condensation,[],[f442])).
% 1.94/0.64  fof(f442,plain,(
% 1.94/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_tarski(X1)) | X0 = X1 | X1 = X2) )),
% 1.94/0.64    inference(resolution,[],[f441,f81])).
% 1.94/0.64  fof(f81,plain,(
% 1.94/0.64    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_enumset1(X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 1.94/0.64    inference(equality_resolution,[],[f62])).
% 1.94/0.64  fof(f62,plain,(
% 1.94/0.64    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.94/0.64    inference(definition_unfolding,[],[f47,f32])).
% 1.94/0.64  fof(f32,plain,(
% 1.94/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.94/0.64    inference(cnf_transformation,[],[f2])).
% 1.94/0.64  fof(f2,axiom,(
% 1.94/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.94/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.94/0.64  fof(f47,plain,(
% 1.94/0.64    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.94/0.64    inference(cnf_transformation,[],[f1])).
% 1.94/0.64  fof(f1,axiom,(
% 1.94/0.64    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.94/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.94/0.64  fof(f441,plain,(
% 1.94/0.64    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_enumset1(X0,X0,X1)) | ~r2_hidden(X1,k1_tarski(X2))) )),
% 1.94/0.64    inference(trivial_inequality_removal,[],[f440])).
% 1.94/0.64  fof(f440,plain,(
% 1.94/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X1) != k1_enumset1(X0,X0,X1) | ~r2_hidden(X1,k1_tarski(X2)) | r2_hidden(X2,k1_enumset1(X0,X0,X1))) )),
% 1.94/0.64    inference(superposition,[],[f67,f38])).
% 1.94/0.64  fof(f38,plain,(
% 1.94/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.94/0.64    inference(cnf_transformation,[],[f4])).
% 1.94/0.64  fof(f4,axiom,(
% 1.94/0.64    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.94/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.94/0.64  fof(f67,plain,(
% 1.94/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X1) != k4_xboole_0(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X1,X2)) )),
% 1.94/0.64    inference(definition_unfolding,[],[f51,f32,f32])).
% 1.94/0.64  fof(f51,plain,(
% 1.94/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.94/0.64    inference(cnf_transformation,[],[f5])).
% 1.94/0.64  fof(f5,axiom,(
% 1.94/0.64    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.94/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 1.94/0.64  fof(f59,plain,(
% 1.94/0.64    ( ! [X4,X2,X0,X3] : (sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 1.94/0.64    inference(definition_unfolding,[],[f29,f40])).
% 1.94/0.64  fof(f40,plain,(
% 1.94/0.64    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.94/0.64    inference(cnf_transformation,[],[f6])).
% 1.94/0.64  fof(f6,axiom,(
% 1.94/0.64    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.94/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.94/0.64  fof(f29,plain,(
% 1.94/0.64    ( ! [X4,X2,X0,X3] : (k1_xboole_0 = X0 | ~r2_hidden(X2,X0) | k3_mcart_1(X2,X3,X4) != sK4(X0)) )),
% 1.94/0.64    inference(cnf_transformation,[],[f18])).
% 1.94/0.64  fof(f991,plain,(
% 1.94/0.64    sK3 = k4_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) | ~spl6_29),
% 1.94/0.64    inference(avatar_component_clause,[],[f989])).
% 1.94/0.64  fof(f989,plain,(
% 1.94/0.64    spl6_29 <=> sK3 = k4_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 1.94/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 1.94/0.64  fof(f495,plain,(
% 1.94/0.64    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 1.94/0.64    inference(condensation,[],[f491])).
% 1.94/0.64  fof(f491,plain,(
% 1.94/0.64    ( ! [X8,X9] : (r2_hidden(X8,k1_tarski(X9)) | r2_hidden(X9,k1_tarski(X9))) )),
% 1.94/0.64    inference(resolution,[],[f487,f80])).
% 1.94/0.64  fof(f80,plain,(
% 1.94/0.64    ( ! [X3,X1] : (r2_hidden(X3,k1_enumset1(X3,X3,X1))) )),
% 1.94/0.64    inference(equality_resolution,[],[f79])).
% 1.94/0.64  fof(f79,plain,(
% 1.94/0.64    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k1_enumset1(X3,X3,X1) != X2) )),
% 1.94/0.64    inference(equality_resolution,[],[f61])).
% 1.94/0.64  fof(f61,plain,(
% 1.94/0.64    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.94/0.64    inference(definition_unfolding,[],[f48,f32])).
% 1.94/0.64  fof(f48,plain,(
% 1.94/0.64    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.94/0.64    inference(cnf_transformation,[],[f1])).
% 1.94/0.64  fof(f487,plain,(
% 1.94/0.64    ( ! [X6,X8,X7] : (~r2_hidden(X8,k1_enumset1(X6,X6,X7)) | r2_hidden(X7,k1_tarski(X8)) | r2_hidden(X6,k1_tarski(X8))) )),
% 1.94/0.64    inference(trivial_inequality_removal,[],[f486])).
% 1.94/0.64  fof(f486,plain,(
% 1.94/0.64    ( ! [X6,X8,X7] : (k1_enumset1(X6,X6,X7) != k1_enumset1(X6,X6,X7) | ~r2_hidden(X8,k1_enumset1(X6,X6,X7)) | r2_hidden(X7,k1_tarski(X8)) | r2_hidden(X6,k1_tarski(X8))) )),
% 1.94/0.64    inference(superposition,[],[f39,f66])).
% 1.94/0.64  fof(f66,plain,(
% 1.94/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X1) = k4_xboole_0(k1_enumset1(X0,X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.94/0.64    inference(definition_unfolding,[],[f52,f32,f32])).
% 1.94/0.64  fof(f52,plain,(
% 1.94/0.64    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X1,X2) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.94/0.64    inference(cnf_transformation,[],[f5])).
% 1.94/0.64  fof(f39,plain,(
% 1.94/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 1.94/0.64    inference(cnf_transformation,[],[f4])).
% 1.94/0.64  fof(f806,plain,(
% 1.94/0.64    k1_xboole_0 != k1_tarski(sK3) | spl6_23),
% 1.94/0.64    inference(avatar_component_clause,[],[f805])).
% 1.94/0.64  fof(f805,plain,(
% 1.94/0.64    spl6_23 <=> k1_xboole_0 = k1_tarski(sK3)),
% 1.94/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.94/0.64  fof(f992,plain,(
% 1.94/0.64    spl6_14 | ~spl6_15 | spl6_16 | spl6_17 | spl6_29 | ~spl6_3),
% 1.94/0.64    inference(avatar_split_clause,[],[f986,f91,f989,f688,f684,f680,f676])).
% 1.94/0.64  fof(f676,plain,(
% 1.94/0.64    spl6_14 <=> k1_xboole_0 = sK0),
% 1.94/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.94/0.64  fof(f680,plain,(
% 1.94/0.64    spl6_15 <=> m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.94/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.94/0.64  fof(f91,plain,(
% 1.94/0.64    spl6_3 <=> sK3 = k5_mcart_1(sK0,sK1,sK2,sK3)),
% 1.94/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.94/0.64  fof(f986,plain,(
% 1.94/0.64    sK3 = k4_tarski(k4_tarski(sK3,k6_mcart_1(sK0,sK1,sK2,sK3)),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0 | ~spl6_3),
% 1.94/0.64    inference(superposition,[],[f69,f93])).
% 1.94/0.64  fof(f93,plain,(
% 1.94/0.64    sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) | ~spl6_3),
% 1.94/0.64    inference(avatar_component_clause,[],[f91])).
% 1.94/0.64  fof(f69,plain,(
% 1.94/0.64    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3)),k7_mcart_1(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0) )),
% 1.94/0.64    inference(definition_unfolding,[],[f53,f41,f40])).
% 1.94/0.64  fof(f41,plain,(
% 1.94/0.64    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.94/0.64    inference(cnf_transformation,[],[f7])).
% 1.94/0.64  fof(f7,axiom,(
% 1.94/0.64    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.94/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.94/0.64  fof(f53,plain,(
% 1.94/0.64    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) )),
% 1.94/0.64    inference(cnf_transformation,[],[f20])).
% 1.94/0.64  fof(f20,plain,(
% 1.94/0.64    ! [X0,X1,X2] : (! [X3] : (k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.94/0.64    inference(ennf_transformation,[],[f11])).
% 1.94/0.64  fof(f11,axiom,(
% 1.94/0.64    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => k3_mcart_1(k5_mcart_1(X0,X1,X2,X3),k6_mcart_1(X0,X1,X2,X3),k7_mcart_1(X0,X1,X2,X3)) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.94/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).
% 1.94/0.64  fof(f963,plain,(
% 1.94/0.64    ~spl6_27),
% 1.94/0.64    inference(avatar_contradiction_clause,[],[f938])).
% 1.94/0.64  fof(f938,plain,(
% 1.94/0.64    $false | ~spl6_27),
% 1.94/0.64    inference(unit_resulting_resolution,[],[f95,f872])).
% 1.94/0.64  fof(f872,plain,(
% 1.94/0.64    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3) | ~spl6_27),
% 1.94/0.64    inference(avatar_component_clause,[],[f870])).
% 1.94/0.64  fof(f870,plain,(
% 1.94/0.64    spl6_27 <=> sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3)),
% 1.94/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 1.94/0.64  fof(f95,plain,(
% 1.94/0.64    ( ! [X2,X1] : (k4_tarski(X1,X2) != X2) )),
% 1.94/0.64    inference(forward_demodulation,[],[f73,f34])).
% 1.94/0.64  fof(f34,plain,(
% 1.94/0.64    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.94/0.64    inference(cnf_transformation,[],[f13])).
% 1.94/0.64  fof(f13,axiom,(
% 1.94/0.64    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.94/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.94/0.64  fof(f73,plain,(
% 1.94/0.64    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 1.94/0.64    inference(equality_resolution,[],[f28])).
% 1.94/0.64  fof(f28,plain,(
% 1.94/0.64    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | k2_mcart_1(X0) != X0) )),
% 1.94/0.64    inference(cnf_transformation,[],[f17])).
% 1.94/0.64  fof(f17,plain,(
% 1.94/0.64    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 1.94/0.64    inference(ennf_transformation,[],[f9])).
% 1.94/0.64  fof(f9,axiom,(
% 1.94/0.64    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.94/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.94/0.64  fof(f873,plain,(
% 1.94/0.64    spl6_14 | ~spl6_15 | spl6_16 | spl6_17 | spl6_27 | ~spl6_1),
% 1.94/0.64    inference(avatar_split_clause,[],[f862,f83,f870,f688,f684,f680,f676])).
% 1.94/0.64  fof(f83,plain,(
% 1.94/0.64    spl6_1 <=> sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)),
% 1.94/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.94/0.64  fof(f862,plain,(
% 1.94/0.64    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),k6_mcart_1(sK0,sK1,sK2,sK3)),sK3) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0 | ~spl6_1),
% 1.94/0.64    inference(superposition,[],[f69,f85])).
% 1.94/0.64  fof(f85,plain,(
% 1.94/0.64    sK3 = k7_mcart_1(sK0,sK1,sK2,sK3) | ~spl6_1),
% 1.94/0.64    inference(avatar_component_clause,[],[f83])).
% 1.94/0.64  fof(f860,plain,(
% 1.94/0.64    ~spl6_4 | ~spl6_23),
% 1.94/0.64    inference(avatar_contradiction_clause,[],[f857])).
% 1.94/0.64  fof(f857,plain,(
% 1.94/0.64    $false | (~spl6_4 | ~spl6_23)),
% 1.94/0.64    inference(unit_resulting_resolution,[],[f218,f840])).
% 1.94/0.64  fof(f840,plain,(
% 1.94/0.64    r2_hidden(sK3,k1_xboole_0) | ~spl6_23),
% 1.94/0.64    inference(superposition,[],[f495,f807])).
% 1.94/0.64  fof(f807,plain,(
% 1.94/0.64    k1_xboole_0 = k1_tarski(sK3) | ~spl6_23),
% 1.94/0.64    inference(avatar_component_clause,[],[f805])).
% 1.94/0.64  fof(f218,plain,(
% 1.94/0.64    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0)) ) | ~spl6_4),
% 1.94/0.64    inference(avatar_component_clause,[],[f217])).
% 1.94/0.64  fof(f217,plain,(
% 1.94/0.64    spl6_4 <=> ! [X3] : ~r2_hidden(X3,k1_xboole_0)),
% 1.94/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.94/0.64  fof(f830,plain,(
% 1.94/0.64    spl6_24),
% 1.94/0.64    inference(avatar_contradiction_clause,[],[f822])).
% 1.94/0.64  fof(f822,plain,(
% 1.94/0.64    $false | spl6_24),
% 1.94/0.64    inference(unit_resulting_resolution,[],[f811,f80,f811,f487])).
% 1.94/0.64  fof(f811,plain,(
% 1.94/0.64    ~r2_hidden(sK3,k1_tarski(sK3)) | spl6_24),
% 1.94/0.64    inference(avatar_component_clause,[],[f809])).
% 1.94/0.64  fof(f809,plain,(
% 1.94/0.64    spl6_24 <=> r2_hidden(sK3,k1_tarski(sK3))),
% 1.94/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.94/0.64  fof(f812,plain,(
% 1.94/0.64    spl6_23 | ~spl6_24 | ~spl6_20),
% 1.94/0.64    inference(avatar_split_clause,[],[f778,f768,f809,f805])).
% 1.94/0.64  fof(f768,plain,(
% 1.94/0.64    spl6_20 <=> sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3))),
% 1.94/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.94/0.64  fof(f778,plain,(
% 1.94/0.64    ~r2_hidden(sK3,k1_tarski(sK3)) | k1_xboole_0 = k1_tarski(sK3) | ~spl6_20),
% 1.94/0.64    inference(superposition,[],[f482,f770])).
% 1.94/0.64  fof(f770,plain,(
% 1.94/0.64    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | ~spl6_20),
% 1.94/0.64    inference(avatar_component_clause,[],[f768])).
% 1.94/0.64  fof(f482,plain,(
% 1.94/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_tarski(k4_tarski(k4_tarski(X1,X0),X2))) | k1_xboole_0 = k1_tarski(k4_tarski(k4_tarski(X1,X0),X2))) )),
% 1.94/0.64    inference(equality_resolution,[],[f451])).
% 1.94/0.64  fof(f451,plain,(
% 1.94/0.64    ( ! [X6,X4,X7,X5] : (k4_tarski(k4_tarski(X5,X6),X7) != X4 | ~r2_hidden(X6,k1_tarski(X4)) | k1_xboole_0 = k1_tarski(X4)) )),
% 1.94/0.64    inference(duplicate_literal_removal,[],[f448])).
% 1.94/0.64  fof(f448,plain,(
% 1.94/0.64    ( ! [X6,X4,X7,X5] : (k4_tarski(k4_tarski(X5,X6),X7) != X4 | ~r2_hidden(X6,k1_tarski(X4)) | k1_xboole_0 = k1_tarski(X4) | k1_xboole_0 = k1_tarski(X4)) )),
% 1.94/0.64    inference(superposition,[],[f58,f444])).
% 1.94/0.64  fof(f58,plain,(
% 1.94/0.64    ( ! [X4,X2,X0,X3] : (sK4(X0) != k4_tarski(k4_tarski(X2,X3),X4) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 1.94/0.64    inference(definition_unfolding,[],[f30,f40])).
% 1.94/0.64  % (19221)Refutation not found, incomplete strategy% (19221)------------------------------
% 1.94/0.64  % (19221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.64  % (19221)Termination reason: Refutation not found, incomplete strategy
% 1.94/0.64  
% 1.94/0.64  % (19221)Memory used [KB]: 2046
% 1.94/0.64  % (19221)Time elapsed: 0.225 s
% 1.94/0.64  % (19221)------------------------------
% 1.94/0.64  % (19221)------------------------------
% 1.94/0.64  fof(f30,plain,(
% 1.94/0.64    ( ! [X4,X2,X0,X3] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | k3_mcart_1(X2,X3,X4) != sK4(X0)) )),
% 1.94/0.64    inference(cnf_transformation,[],[f18])).
% 1.94/0.64  fof(f771,plain,(
% 1.94/0.64    spl6_14 | ~spl6_15 | spl6_16 | spl6_17 | spl6_20 | ~spl6_2),
% 1.94/0.64    inference(avatar_split_clause,[],[f742,f87,f768,f688,f684,f680,f676])).
% 1.94/0.64  fof(f87,plain,(
% 1.94/0.64    spl6_2 <=> sK3 = k6_mcart_1(sK0,sK1,sK2,sK3)),
% 1.94/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.94/0.64  fof(f742,plain,(
% 1.94/0.64    sK3 = k4_tarski(k4_tarski(k5_mcart_1(sK0,sK1,sK2,sK3),sK3),k7_mcart_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK0 | ~spl6_2),
% 1.94/0.64    inference(superposition,[],[f69,f89])).
% 1.94/0.64  fof(f89,plain,(
% 1.94/0.64    sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | ~spl6_2),
% 1.94/0.64    inference(avatar_component_clause,[],[f87])).
% 1.94/0.64  fof(f733,plain,(
% 1.94/0.64    ~spl6_14),
% 1.94/0.64    inference(avatar_contradiction_clause,[],[f731])).
% 1.94/0.64  fof(f731,plain,(
% 1.94/0.64    $false | ~spl6_14),
% 1.94/0.64    inference(subsumption_resolution,[],[f24,f678])).
% 1.94/0.64  fof(f678,plain,(
% 1.94/0.64    k1_xboole_0 = sK0 | ~spl6_14),
% 1.94/0.64    inference(avatar_component_clause,[],[f676])).
% 1.94/0.64  fof(f24,plain,(
% 1.94/0.64    k1_xboole_0 != sK0),
% 1.94/0.64    inference(cnf_transformation,[],[f16])).
% 1.94/0.64  fof(f698,plain,(
% 1.94/0.64    spl6_15),
% 1.94/0.64    inference(avatar_contradiction_clause,[],[f697])).
% 1.94/0.64  fof(f697,plain,(
% 1.94/0.64    $false | spl6_15),
% 1.94/0.64    inference(subsumption_resolution,[],[f57,f682])).
% 1.94/0.64  fof(f682,plain,(
% 1.94/0.64    ~m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | spl6_15),
% 1.94/0.64    inference(avatar_component_clause,[],[f680])).
% 1.94/0.64  fof(f57,plain,(
% 1.94/0.64    m1_subset_1(sK3,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 1.94/0.64    inference(definition_unfolding,[],[f23,f41])).
% 1.94/0.64  fof(f23,plain,(
% 1.94/0.64    m1_subset_1(sK3,k3_zfmisc_1(sK0,sK1,sK2))),
% 1.94/0.64    inference(cnf_transformation,[],[f16])).
% 1.94/0.64  fof(f343,plain,(
% 1.94/0.64    ~spl6_8),
% 1.94/0.64    inference(avatar_contradiction_clause,[],[f289])).
% 1.94/0.64  fof(f289,plain,(
% 1.94/0.64    $false | ~spl6_8),
% 1.94/0.64    inference(subsumption_resolution,[],[f96,f282])).
% 1.94/0.64  fof(f282,plain,(
% 1.94/0.64    ( ! [X0,X1] : (X0 = X1) ) | ~spl6_8),
% 1.94/0.64    inference(condensation,[],[f268])).
% 1.94/0.64  fof(f268,plain,(
% 1.94/0.64    ( ! [X0,X3,X1] : (X1 = X3 | X0 = X3) ) | ~spl6_8),
% 1.94/0.64    inference(subsumption_resolution,[],[f81,f233])).
% 1.94/0.64  fof(f233,plain,(
% 1.94/0.64    ( ! [X8,X7] : (r2_hidden(X7,X8)) ) | ~spl6_8),
% 1.94/0.64    inference(avatar_component_clause,[],[f232])).
% 1.94/0.64  fof(f232,plain,(
% 1.94/0.64    spl6_8 <=> ! [X7,X8] : r2_hidden(X7,X8)),
% 1.94/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.94/0.64  fof(f96,plain,(
% 1.94/0.64    ( ! [X2,X1] : (k4_tarski(X1,X2) != X1) )),
% 1.94/0.64    inference(forward_demodulation,[],[f74,f33])).
% 1.94/0.64  fof(f33,plain,(
% 1.94/0.64    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.94/0.64    inference(cnf_transformation,[],[f13])).
% 1.94/0.64  fof(f74,plain,(
% 1.94/0.64    ( ! [X2,X1] : (k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2))) )),
% 1.94/0.64    inference(equality_resolution,[],[f27])).
% 1.94/0.64  fof(f27,plain,(
% 1.94/0.64    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | k1_mcart_1(X0) != X0) )),
% 1.94/0.64    inference(cnf_transformation,[],[f17])).
% 1.94/0.64  fof(f234,plain,(
% 1.94/0.64    spl6_4 | spl6_8),
% 1.94/0.64    inference(avatar_split_clause,[],[f211,f232,f217])).
% 1.94/0.64  fof(f211,plain,(
% 1.94/0.64    ( ! [X6,X8,X7] : (r2_hidden(X7,X8) | ~r2_hidden(X6,k1_xboole_0)) )),
% 1.94/0.64    inference(duplicate_literal_removal,[],[f150])).
% 1.94/0.64  fof(f150,plain,(
% 1.94/0.64    ( ! [X6,X8,X7] : (r2_hidden(X7,X8) | ~r2_hidden(X6,k1_xboole_0) | ~r2_hidden(X6,k1_xboole_0)) )),
% 1.94/0.64    inference(superposition,[],[f109,f140])).
% 1.94/0.64  fof(f140,plain,(
% 1.94/0.64    ( ! [X0,X1] : (k2_mcart_1(X0) = X1 | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.94/0.64    inference(condensation,[],[f135])).
% 1.94/0.64  fof(f135,plain,(
% 1.94/0.64    ( ! [X19,X20,X18] : (k2_mcart_1(X19) = X18 | k2_mcart_1(X19) = X20 | ~r2_hidden(X19,k1_xboole_0)) )),
% 1.94/0.64    inference(resolution,[],[f81,f109])).
% 1.94/0.64  fof(f109,plain,(
% 1.94/0.64    ( ! [X2,X3] : (r2_hidden(k2_mcart_1(X3),X2) | ~r2_hidden(X3,k1_xboole_0)) )),
% 1.94/0.64    inference(superposition,[],[f43,f76])).
% 1.94/0.64  fof(f76,plain,(
% 1.94/0.64    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.94/0.64    inference(equality_resolution,[],[f36])).
% 1.94/0.64  fof(f36,plain,(
% 1.94/0.64    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.94/0.64    inference(cnf_transformation,[],[f3])).
% 1.94/0.64  fof(f3,axiom,(
% 1.94/0.64    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.94/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.94/0.64  fof(f43,plain,(
% 1.94/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.94/0.64    inference(cnf_transformation,[],[f19])).
% 1.94/0.64  fof(f19,plain,(
% 1.94/0.64    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.94/0.64    inference(ennf_transformation,[],[f8])).
% 1.94/0.64  fof(f8,axiom,(
% 1.94/0.64    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.94/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.94/0.64  fof(f94,plain,(
% 1.94/0.64    spl6_1 | spl6_2 | spl6_3),
% 1.94/0.64    inference(avatar_split_clause,[],[f22,f91,f87,f83])).
% 1.94/0.64  fof(f22,plain,(
% 1.94/0.64    sK3 = k5_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k6_mcart_1(sK0,sK1,sK2,sK3) | sK3 = k7_mcart_1(sK0,sK1,sK2,sK3)),
% 1.94/0.64    inference(cnf_transformation,[],[f16])).
% 1.94/0.64  % SZS output end Proof for theBenchmark
% 1.94/0.64  % (19233)------------------------------
% 1.94/0.64  % (19233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.64  % (19233)Termination reason: Refutation
% 1.94/0.64  
% 1.94/0.64  % (19233)Memory used [KB]: 6908
% 1.94/0.64  % (19233)Time elapsed: 0.196 s
% 1.94/0.64  % (19233)------------------------------
% 1.94/0.64  % (19233)------------------------------
% 1.94/0.65  % (19219)Success in time 0.275 s
%------------------------------------------------------------------------------
