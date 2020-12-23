%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:32 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 701 expanded)
%              Number of leaves         :   29 ( 238 expanded)
%              Depth                    :   15
%              Number of atoms          :  403 (1270 expanded)
%              Number of equality atoms :  220 (1042 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1101,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f120,f125,f135,f136,f211,f854,f988,f1065,f1100])).

fof(f1100,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f1094])).

fof(f1094,plain,
    ( $false
    | spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f1067,f1069])).

fof(f1069,plain,
    ( ! [X1] : r1_tarski(sK0,k4_enumset1(X1,X1,X1,X1,X1,sK2))
    | ~ spl5_4 ),
    inference(superposition,[],[f99,f118])).

fof(f118,plain,
    ( sK0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_4
  <=> sK0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f99,plain,(
    ! [X2,X1] : r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2))
      | k4_enumset1(X2,X2,X2,X2,X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f72,f78,f82])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f78])).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f1067,plain,
    ( ~ r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))
    | spl5_3 ),
    inference(subsumption_resolution,[],[f1066,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f1066,plain,
    ( k1_xboole_0 != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))
    | spl5_3 ),
    inference(forward_demodulation,[],[f1060,f208])).

fof(f208,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f185,f201])).

fof(f201,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f194,f49])).

fof(f49,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f194,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f185,f48])).

fof(f185,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f68,f48])).

fof(f68,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1060,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))))
    | ~ r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))
    | spl5_3 ),
    inference(superposition,[],[f991,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f78])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f991,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))))))
    | spl5_3 ),
    inference(forward_demodulation,[],[f115,f68])).

fof(f115,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_3
  <=> k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1065,plain,
    ( spl5_3
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f1064])).

fof(f1064,plain,
    ( $false
    | spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f1063,f208])).

fof(f1063,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0))
    | spl5_3
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f1062,f48])).

fof(f1062,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))))
    | spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f1060,f992])).

fof(f992,plain,
    ( ! [X0] : r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,X0))
    | ~ spl5_5 ),
    inference(superposition,[],[f100,f123])).

fof(f123,plain,
    ( sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl5_5
  <=> sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f100,plain,(
    ! [X2,X1] : r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2))
      | k4_enumset1(X1,X1,X1,X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f71,f78,f82])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f988,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f987])).

fof(f987,plain,
    ( $false
    | spl5_6 ),
    inference(subsumption_resolution,[],[f986,f48])).

fof(f986,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl5_6 ),
    inference(forward_demodulation,[],[f985,f48])).

fof(f985,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))
    | spl5_6 ),
    inference(subsumption_resolution,[],[f982,f145])).

fof(f145,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(resolution,[],[f142,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f142,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f62,f97])).

fof(f97,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f982,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))
    | ~ r1_tarski(k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))
    | spl5_6 ),
    inference(superposition,[],[f856,f91])).

fof(f856,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))))
    | spl5_6 ),
    inference(forward_demodulation,[],[f855,f201])).

fof(f855,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))))))
    | spl5_6 ),
    inference(forward_demodulation,[],[f130,f68])).

fof(f130,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl5_6
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f854,plain,
    ( spl5_7
    | spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f853,f122,f117,f113,f108,f132])).

fof(f132,plain,
    ( spl5_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f108,plain,
    ( spl5_2
  <=> sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f853,plain,
    ( k1_xboole_0 = sK0
    | spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f849,f110])).

fof(f110,plain,
    ( sK0 != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f849,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)
    | ~ spl5_3
    | spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f848,f124])).

fof(f124,plain,
    ( sK0 != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f848,plain,
    ( sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f837,f119])).

fof(f119,plain,
    ( sK0 != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f837,plain,
    ( sK0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f96,f362])).

fof(f362,plain,
    ( r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl5_3 ),
    inference(superposition,[],[f90,f359])).

fof(f359,plain,
    ( k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2) = k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f354,f49])).

fof(f354,plain,
    ( k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) = k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0)
    | ~ spl5_3 ),
    inference(superposition,[],[f208,f228])).

fof(f228,plain,
    ( k1_xboole_0 = k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))))
    | ~ spl5_3 ),
    inference(superposition,[],[f208,f212])).

fof(f212,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))))))
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f114,f68])).

fof(f114,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f90,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f55,f79])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2))
      | k4_enumset1(X2,X2,X2,X2,X2,X2) = X0
      | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | k4_enumset1(X1,X1,X1,X1,X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f69,f78,f82,f82,f78])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f211,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f207,f48])).

fof(f207,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | spl5_1 ),
    inference(backward_demodulation,[],[f177,f201])).

fof(f177,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,sK0))
    | spl5_1 ),
    inference(backward_demodulation,[],[f138,f89])).

fof(f89,plain,(
    ! [X0] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f54,f79])).

fof(f54,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f138,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl5_1 ),
    inference(forward_demodulation,[],[f106,f48])).

fof(f106,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK0),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_1
  <=> k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK0),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f136,plain,
    ( spl5_3
    | spl5_7
    | spl5_5
    | spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f87,f108,f117,f122,f132,f113])).

fof(f87,plain,
    ( sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)
    | sK0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))))) ),
    inference(definition_unfolding,[],[f43,f78,f82,f82,f81,f78])).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f58,f80])).

fof(f80,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f59,f79])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ( sK0 != k2_tarski(sK1,sK2)
        & sK0 != k1_tarski(sK2)
        & sK0 != k1_tarski(sK1)
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) )
    & ( sK0 = k2_tarski(sK1,sK2)
      | sK0 = k1_tarski(sK2)
      | sK0 = k1_tarski(sK1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ( ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
        & ( k2_tarski(X1,X2) = X0
          | k1_tarski(X2) = X0
          | k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) )
   => ( ( ( sK0 != k2_tarski(sK1,sK2)
          & sK0 != k1_tarski(sK2)
          & sK0 != k1_tarski(sK1)
          & k1_xboole_0 != sK0 )
        | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) )
      & ( sK0 = k2_tarski(sK1,sK2)
        | sK0 = k1_tarski(sK2)
        | sK0 = k1_tarski(sK1)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f135,plain,
    ( ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f126,f132,f128])).

fof(f126,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))))) ),
    inference(inner_rewriting,[],[f86])).

fof(f86,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))))) ),
    inference(definition_unfolding,[],[f44,f81,f78])).

fof(f44,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f125,plain,
    ( ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f85,f122,f113])).

fof(f85,plain,
    ( sK0 != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))))) ),
    inference(definition_unfolding,[],[f45,f82,f81,f78])).

fof(f45,plain,
    ( sK0 != k1_tarski(sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f120,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f84,f117,f113])).

fof(f84,plain,
    ( sK0 != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))))) ),
    inference(definition_unfolding,[],[f46,f82,f81,f78])).

fof(f46,plain,
    ( sK0 != k1_tarski(sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f111,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f102,f108,f104])).

fof(f102,plain,
    ( sK0 != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)
    | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK0),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(inner_rewriting,[],[f83])).

fof(f83,plain,
    ( sK0 != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)
    | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))))) ),
    inference(definition_unfolding,[],[f47,f78,f81,f78])).

fof(f47,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:02:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (1540)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (1556)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (1561)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (1544)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (1553)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (1561)Refutation not found, incomplete strategy% (1561)------------------------------
% 0.21/0.52  % (1561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1548)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (1543)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (1564)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (1550)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (1545)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (1557)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (1550)Refutation not found, incomplete strategy% (1550)------------------------------
% 0.21/0.53  % (1550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1550)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1550)Memory used [KB]: 10618
% 0.21/0.53  % (1550)Time elapsed: 0.113 s
% 0.21/0.53  % (1550)------------------------------
% 0.21/0.53  % (1550)------------------------------
% 0.21/0.53  % (1557)Refutation not found, incomplete strategy% (1557)------------------------------
% 0.21/0.53  % (1557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1557)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1557)Memory used [KB]: 10618
% 0.21/0.53  % (1557)Time elapsed: 0.133 s
% 0.21/0.53  % (1557)------------------------------
% 0.21/0.53  % (1557)------------------------------
% 0.21/0.53  % (1561)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1561)Memory used [KB]: 1791
% 0.21/0.53  % (1561)Time elapsed: 0.118 s
% 0.21/0.53  % (1561)------------------------------
% 0.21/0.53  % (1561)------------------------------
% 0.21/0.53  % (1546)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (1551)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (1551)Refutation not found, incomplete strategy% (1551)------------------------------
% 0.21/0.54  % (1551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1551)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1551)Memory used [KB]: 10746
% 0.21/0.54  % (1551)Time elapsed: 0.135 s
% 0.21/0.54  % (1551)------------------------------
% 0.21/0.54  % (1551)------------------------------
% 0.21/0.54  % (1547)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (1565)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (1569)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (1542)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (1563)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (1542)Refutation not found, incomplete strategy% (1542)------------------------------
% 0.21/0.54  % (1542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1542)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1542)Memory used [KB]: 10746
% 0.21/0.54  % (1542)Time elapsed: 0.136 s
% 0.21/0.54  % (1542)------------------------------
% 0.21/0.54  % (1542)------------------------------
% 0.21/0.54  % (1548)Refutation not found, incomplete strategy% (1548)------------------------------
% 0.21/0.54  % (1548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1548)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1548)Memory used [KB]: 10746
% 0.21/0.54  % (1548)Time elapsed: 0.136 s
% 0.21/0.54  % (1548)------------------------------
% 0.21/0.54  % (1548)------------------------------
% 0.21/0.54  % (1562)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (1541)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (1568)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (1558)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (1554)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (1567)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (1560)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (1566)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (1555)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (1552)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (1559)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (1549)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.74/0.61  % (1567)Refutation found. Thanks to Tanya!
% 1.74/0.61  % SZS status Theorem for theBenchmark
% 1.74/0.61  % SZS output start Proof for theBenchmark
% 1.74/0.61  fof(f1101,plain,(
% 1.74/0.61    $false),
% 1.74/0.61    inference(avatar_sat_refutation,[],[f111,f120,f125,f135,f136,f211,f854,f988,f1065,f1100])).
% 1.74/0.61  fof(f1100,plain,(
% 1.74/0.61    spl5_3 | ~spl5_4),
% 1.74/0.61    inference(avatar_contradiction_clause,[],[f1094])).
% 1.74/0.61  fof(f1094,plain,(
% 1.74/0.61    $false | (spl5_3 | ~spl5_4)),
% 1.74/0.61    inference(subsumption_resolution,[],[f1067,f1069])).
% 1.74/0.61  fof(f1069,plain,(
% 1.74/0.61    ( ! [X1] : (r1_tarski(sK0,k4_enumset1(X1,X1,X1,X1,X1,sK2))) ) | ~spl5_4),
% 1.74/0.61    inference(superposition,[],[f99,f118])).
% 1.74/0.61  fof(f118,plain,(
% 1.74/0.61    sK0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) | ~spl5_4),
% 1.74/0.61    inference(avatar_component_clause,[],[f117])).
% 1.74/0.61  fof(f117,plain,(
% 1.74/0.61    spl5_4 <=> sK0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2)),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.74/0.61  fof(f99,plain,(
% 1.74/0.61    ( ! [X2,X1] : (r1_tarski(k4_enumset1(X2,X2,X2,X2,X2,X2),k4_enumset1(X1,X1,X1,X1,X1,X2))) )),
% 1.74/0.61    inference(equality_resolution,[],[f93])).
% 1.74/0.61  fof(f93,plain,(
% 1.74/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2)) | k4_enumset1(X2,X2,X2,X2,X2,X2) != X0) )),
% 1.74/0.61    inference(definition_unfolding,[],[f72,f78,f82])).
% 1.74/0.61  fof(f82,plain,(
% 1.74/0.61    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.74/0.61    inference(definition_unfolding,[],[f50,f78])).
% 1.74/0.61  fof(f50,plain,(
% 1.74/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f13])).
% 1.74/0.61  fof(f13,axiom,(
% 1.74/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.74/0.61  fof(f78,plain,(
% 1.74/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.74/0.61    inference(definition_unfolding,[],[f57,f77])).
% 1.74/0.61  fof(f77,plain,(
% 1.74/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.74/0.61    inference(definition_unfolding,[],[f67,f76])).
% 1.74/0.61  fof(f76,plain,(
% 1.74/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.74/0.61    inference(definition_unfolding,[],[f74,f75])).
% 1.74/0.61  fof(f75,plain,(
% 1.74/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f17])).
% 1.74/0.61  fof(f17,axiom,(
% 1.74/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.74/0.61  fof(f74,plain,(
% 1.74/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f16])).
% 1.74/0.61  fof(f16,axiom,(
% 1.74/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.74/0.61  fof(f67,plain,(
% 1.74/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f15])).
% 1.74/0.61  fof(f15,axiom,(
% 1.74/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.74/0.61  fof(f57,plain,(
% 1.74/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f14])).
% 1.74/0.61  fof(f14,axiom,(
% 1.74/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.74/0.61  fof(f72,plain,(
% 1.74/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 1.74/0.61    inference(cnf_transformation,[],[f42])).
% 1.74/0.61  fof(f42,plain,(
% 1.74/0.61    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.74/0.61    inference(flattening,[],[f41])).
% 1.74/0.61  fof(f41,plain,(
% 1.74/0.61    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.74/0.61    inference(nnf_transformation,[],[f30])).
% 1.74/0.61  fof(f30,plain,(
% 1.74/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.74/0.61    inference(ennf_transformation,[],[f18])).
% 1.74/0.61  fof(f18,axiom,(
% 1.74/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.74/0.61  fof(f1067,plain,(
% 1.74/0.61    ~r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)) | spl5_3),
% 1.74/0.61    inference(subsumption_resolution,[],[f1066,f48])).
% 1.74/0.61  fof(f48,plain,(
% 1.74/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f11])).
% 1.74/0.61  fof(f11,axiom,(
% 1.74/0.61    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.74/0.61  fof(f1066,plain,(
% 1.74/0.61    k1_xboole_0 != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)) | ~r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)) | spl5_3),
% 1.74/0.61    inference(forward_demodulation,[],[f1060,f208])).
% 1.74/0.61  fof(f208,plain,(
% 1.74/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.74/0.61    inference(backward_demodulation,[],[f185,f201])).
% 1.74/0.61  fof(f201,plain,(
% 1.74/0.61    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.74/0.61    inference(forward_demodulation,[],[f194,f49])).
% 1.74/0.61  fof(f49,plain,(
% 1.74/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.74/0.61    inference(cnf_transformation,[],[f7])).
% 1.74/0.61  fof(f7,axiom,(
% 1.74/0.61    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.74/0.61  fof(f194,plain,(
% 1.74/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.74/0.61    inference(superposition,[],[f185,f48])).
% 1.74/0.61  fof(f185,plain,(
% 1.74/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 1.74/0.61    inference(superposition,[],[f68,f48])).
% 1.74/0.61  fof(f68,plain,(
% 1.74/0.61    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.74/0.61    inference(cnf_transformation,[],[f10])).
% 1.74/0.61  fof(f10,axiom,(
% 1.74/0.61    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.74/0.61  fof(f1060,plain,(
% 1.74/0.61    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))) | ~r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)) | spl5_3),
% 1.74/0.61    inference(superposition,[],[f991,f91])).
% 1.74/0.61  fof(f91,plain,(
% 1.74/0.61    ( ! [X0,X1] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.74/0.61    inference(definition_unfolding,[],[f63,f79])).
% 1.74/0.61  fof(f79,plain,(
% 1.74/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.74/0.61    inference(definition_unfolding,[],[f56,f78])).
% 1.74/0.61  fof(f56,plain,(
% 1.74/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.74/0.61    inference(cnf_transformation,[],[f19])).
% 1.74/0.61  fof(f19,axiom,(
% 1.74/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.74/0.61  fof(f63,plain,(
% 1.74/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f28])).
% 1.74/0.61  fof(f28,plain,(
% 1.74/0.61    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.74/0.61    inference(ennf_transformation,[],[f6])).
% 1.74/0.61  fof(f6,axiom,(
% 1.74/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.74/0.61  fof(f991,plain,(
% 1.74/0.61    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))))) | spl5_3),
% 1.74/0.61    inference(forward_demodulation,[],[f115,f68])).
% 1.74/0.61  fof(f115,plain,(
% 1.74/0.61    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))))) | spl5_3),
% 1.74/0.61    inference(avatar_component_clause,[],[f113])).
% 1.74/0.61  fof(f113,plain,(
% 1.74/0.61    spl5_3 <=> k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))))),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.74/0.61  fof(f1065,plain,(
% 1.74/0.61    spl5_3 | ~spl5_5),
% 1.74/0.61    inference(avatar_contradiction_clause,[],[f1064])).
% 1.74/0.61  fof(f1064,plain,(
% 1.74/0.61    $false | (spl5_3 | ~spl5_5)),
% 1.74/0.61    inference(subsumption_resolution,[],[f1063,f208])).
% 1.74/0.61  fof(f1063,plain,(
% 1.74/0.61    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0)) | (spl5_3 | ~spl5_5)),
% 1.74/0.61    inference(forward_demodulation,[],[f1062,f48])).
% 1.74/0.61  fof(f1062,plain,(
% 1.74/0.61    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))) | (spl5_3 | ~spl5_5)),
% 1.74/0.61    inference(subsumption_resolution,[],[f1060,f992])).
% 1.74/0.61  fof(f992,plain,(
% 1.74/0.61    ( ! [X0] : (r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,X0))) ) | ~spl5_5),
% 1.74/0.61    inference(superposition,[],[f100,f123])).
% 1.74/0.61  fof(f123,plain,(
% 1.74/0.61    sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | ~spl5_5),
% 1.74/0.61    inference(avatar_component_clause,[],[f122])).
% 1.74/0.61  fof(f122,plain,(
% 1.74/0.61    spl5_5 <=> sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.74/0.61  fof(f100,plain,(
% 1.74/0.61    ( ! [X2,X1] : (r1_tarski(k4_enumset1(X1,X1,X1,X1,X1,X1),k4_enumset1(X1,X1,X1,X1,X1,X2))) )),
% 1.74/0.61    inference(equality_resolution,[],[f94])).
% 1.74/0.61  fof(f94,plain,(
% 1.74/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2)) | k4_enumset1(X1,X1,X1,X1,X1,X1) != X0) )),
% 1.74/0.61    inference(definition_unfolding,[],[f71,f78,f82])).
% 1.74/0.61  fof(f71,plain,(
% 1.74/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 1.74/0.61    inference(cnf_transformation,[],[f42])).
% 1.74/0.61  fof(f988,plain,(
% 1.74/0.61    spl5_6),
% 1.74/0.61    inference(avatar_contradiction_clause,[],[f987])).
% 1.74/0.61  fof(f987,plain,(
% 1.74/0.61    $false | spl5_6),
% 1.74/0.61    inference(subsumption_resolution,[],[f986,f48])).
% 1.74/0.61  fof(f986,plain,(
% 1.74/0.61    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | spl5_6),
% 1.74/0.61    inference(forward_demodulation,[],[f985,f48])).
% 1.74/0.61  fof(f985,plain,(
% 1.74/0.61    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) | spl5_6),
% 1.74/0.61    inference(subsumption_resolution,[],[f982,f145])).
% 1.74/0.61  fof(f145,plain,(
% 1.74/0.61    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 1.74/0.61    inference(resolution,[],[f142,f65])).
% 1.74/0.61  fof(f65,plain,(
% 1.74/0.61    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f40])).
% 1.74/0.61  fof(f40,plain,(
% 1.74/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.74/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).
% 1.74/0.61  fof(f39,plain,(
% 1.74/0.61    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.74/0.61    introduced(choice_axiom,[])).
% 1.74/0.61  fof(f38,plain,(
% 1.74/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.74/0.61    inference(rectify,[],[f37])).
% 1.74/0.61  fof(f37,plain,(
% 1.74/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.74/0.61    inference(nnf_transformation,[],[f29])).
% 1.74/0.61  fof(f29,plain,(
% 1.74/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.74/0.61    inference(ennf_transformation,[],[f1])).
% 1.74/0.61  fof(f1,axiom,(
% 1.74/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.74/0.61  fof(f142,plain,(
% 1.74/0.61    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.74/0.61    inference(duplicate_literal_removal,[],[f141])).
% 1.74/0.61  fof(f141,plain,(
% 1.74/0.61    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.74/0.61    inference(resolution,[],[f62,f97])).
% 1.74/0.61  fof(f97,plain,(
% 1.74/0.61    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.74/0.61    inference(equality_resolution,[],[f51])).
% 1.74/0.61  fof(f51,plain,(
% 1.74/0.61    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f26])).
% 1.74/0.61  fof(f26,plain,(
% 1.74/0.61    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.74/0.61    inference(ennf_transformation,[],[f8])).
% 1.74/0.61  fof(f8,axiom,(
% 1.74/0.61    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.74/0.61  fof(f62,plain,(
% 1.74/0.61    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.74/0.61    inference(cnf_transformation,[],[f36])).
% 1.74/0.61  fof(f36,plain,(
% 1.74/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.74/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f35])).
% 1.74/0.61  fof(f35,plain,(
% 1.74/0.61    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.74/0.61    introduced(choice_axiom,[])).
% 1.74/0.61  fof(f27,plain,(
% 1.74/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.74/0.61    inference(ennf_transformation,[],[f24])).
% 1.74/0.61  fof(f24,plain,(
% 1.74/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.74/0.61    inference(rectify,[],[f4])).
% 1.74/0.61  fof(f4,axiom,(
% 1.74/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.74/0.61  fof(f982,plain,(
% 1.74/0.61    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) | ~r1_tarski(k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)) | spl5_6),
% 1.74/0.61    inference(superposition,[],[f856,f91])).
% 1.74/0.61  fof(f856,plain,(
% 1.74/0.61    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))))) | spl5_6),
% 1.74/0.61    inference(forward_demodulation,[],[f855,f201])).
% 1.74/0.61  fof(f855,plain,(
% 1.74/0.61    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))))) | spl5_6),
% 1.74/0.61    inference(forward_demodulation,[],[f130,f68])).
% 1.74/0.61  fof(f130,plain,(
% 1.74/0.61    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))))) | spl5_6),
% 1.74/0.61    inference(avatar_component_clause,[],[f128])).
% 1.74/0.61  fof(f128,plain,(
% 1.74/0.61    spl5_6 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))))),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.74/0.61  fof(f854,plain,(
% 1.74/0.61    spl5_7 | spl5_2 | ~spl5_3 | spl5_4 | spl5_5),
% 1.74/0.61    inference(avatar_split_clause,[],[f853,f122,f117,f113,f108,f132])).
% 1.74/0.61  fof(f132,plain,(
% 1.74/0.61    spl5_7 <=> k1_xboole_0 = sK0),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.74/0.61  fof(f108,plain,(
% 1.74/0.61    spl5_2 <=> sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.74/0.61  fof(f853,plain,(
% 1.74/0.61    k1_xboole_0 = sK0 | (spl5_2 | ~spl5_3 | spl5_4 | spl5_5)),
% 1.74/0.61    inference(subsumption_resolution,[],[f849,f110])).
% 1.74/0.61  fof(f110,plain,(
% 1.74/0.61    sK0 != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2) | spl5_2),
% 1.74/0.61    inference(avatar_component_clause,[],[f108])).
% 1.74/0.61  fof(f849,plain,(
% 1.74/0.61    k1_xboole_0 = sK0 | sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2) | (~spl5_3 | spl5_4 | spl5_5)),
% 1.74/0.61    inference(subsumption_resolution,[],[f848,f124])).
% 1.74/0.61  fof(f124,plain,(
% 1.74/0.61    sK0 != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | spl5_5),
% 1.74/0.61    inference(avatar_component_clause,[],[f122])).
% 1.74/0.61  fof(f848,plain,(
% 1.74/0.61    sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0 | sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2) | (~spl5_3 | spl5_4)),
% 1.74/0.61    inference(subsumption_resolution,[],[f837,f119])).
% 1.74/0.61  fof(f119,plain,(
% 1.74/0.61    sK0 != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) | spl5_4),
% 1.74/0.61    inference(avatar_component_clause,[],[f117])).
% 1.74/0.61  fof(f837,plain,(
% 1.74/0.61    sK0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) | sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0 | sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2) | ~spl5_3),
% 1.74/0.61    inference(resolution,[],[f96,f362])).
% 1.74/0.61  fof(f362,plain,(
% 1.74/0.61    r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl5_3),
% 1.74/0.61    inference(superposition,[],[f90,f359])).
% 1.74/0.61  fof(f359,plain,(
% 1.74/0.61    k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2) = k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) | ~spl5_3),
% 1.74/0.61    inference(forward_demodulation,[],[f354,f49])).
% 1.74/0.61  fof(f354,plain,(
% 1.74/0.61    k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))) = k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0) | ~spl5_3),
% 1.74/0.61    inference(superposition,[],[f208,f228])).
% 1.74/0.61  fof(f228,plain,(
% 1.74/0.61    k1_xboole_0 = k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))) | ~spl5_3),
% 1.74/0.61    inference(superposition,[],[f208,f212])).
% 1.74/0.61  fof(f212,plain,(
% 1.74/0.61    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))))) | ~spl5_3),
% 1.74/0.61    inference(forward_demodulation,[],[f114,f68])).
% 1.74/0.61  fof(f114,plain,(
% 1.74/0.61    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2))))) | ~spl5_3),
% 1.74/0.61    inference(avatar_component_clause,[],[f113])).
% 1.74/0.61  fof(f90,plain,(
% 1.74/0.61    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 1.74/0.61    inference(definition_unfolding,[],[f55,f79])).
% 1.74/0.61  fof(f55,plain,(
% 1.74/0.61    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.74/0.61    inference(cnf_transformation,[],[f9])).
% 1.74/0.61  fof(f9,axiom,(
% 1.74/0.61    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.74/0.61  fof(f96,plain,(
% 1.74/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X2)) | k4_enumset1(X2,X2,X2,X2,X2,X2) = X0 | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | k4_enumset1(X1,X1,X1,X1,X1,X2) = X0) )),
% 1.74/0.61    inference(definition_unfolding,[],[f69,f78,f82,f82,f78])).
% 1.74/0.61  fof(f69,plain,(
% 1.74/0.61    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.74/0.61    inference(cnf_transformation,[],[f42])).
% 1.74/0.61  fof(f211,plain,(
% 1.74/0.61    spl5_1),
% 1.74/0.61    inference(avatar_contradiction_clause,[],[f210])).
% 1.74/0.61  fof(f210,plain,(
% 1.74/0.61    $false | spl5_1),
% 1.74/0.61    inference(subsumption_resolution,[],[f207,f48])).
% 1.74/0.61  fof(f207,plain,(
% 1.74/0.61    k1_xboole_0 != k5_xboole_0(sK0,sK0) | spl5_1),
% 1.74/0.61    inference(backward_demodulation,[],[f177,f201])).
% 1.74/0.61  fof(f177,plain,(
% 1.74/0.61    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,sK0)) | spl5_1),
% 1.74/0.61    inference(backward_demodulation,[],[f138,f89])).
% 1.74/0.61  fof(f89,plain,(
% 1.74/0.61    ( ! [X0] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.74/0.61    inference(definition_unfolding,[],[f54,f79])).
% 1.74/0.61  fof(f54,plain,(
% 1.74/0.61    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.74/0.61    inference(cnf_transformation,[],[f23])).
% 1.74/0.61  fof(f23,plain,(
% 1.74/0.61    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.74/0.61    inference(rectify,[],[f2])).
% 1.74/0.61  fof(f2,axiom,(
% 1.74/0.61    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.74/0.61  fof(f138,plain,(
% 1.74/0.61    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) | spl5_1),
% 1.74/0.61    inference(forward_demodulation,[],[f106,f48])).
% 1.74/0.61  fof(f106,plain,(
% 1.74/0.61    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK0),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) | spl5_1),
% 1.74/0.61    inference(avatar_component_clause,[],[f104])).
% 1.74/0.61  fof(f104,plain,(
% 1.74/0.61    spl5_1 <=> k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK0),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.74/0.61  fof(f136,plain,(
% 1.74/0.61    spl5_3 | spl5_7 | spl5_5 | spl5_4 | spl5_2),
% 1.74/0.61    inference(avatar_split_clause,[],[f87,f108,f117,f122,f132,f113])).
% 1.74/0.61  fof(f87,plain,(
% 1.74/0.61    sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2) | sK0 = k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) | sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))))),
% 1.74/0.61    inference(definition_unfolding,[],[f43,f78,f82,f82,f81,f78])).
% 1.74/0.61  fof(f81,plain,(
% 1.74/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))))) )),
% 1.74/0.61    inference(definition_unfolding,[],[f58,f80])).
% 1.74/0.61  fof(f80,plain,(
% 1.74/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 1.74/0.61    inference(definition_unfolding,[],[f59,f79])).
% 1.74/0.61  fof(f59,plain,(
% 1.74/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.74/0.61    inference(cnf_transformation,[],[f12])).
% 1.74/0.61  fof(f12,axiom,(
% 1.74/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.74/0.61  fof(f58,plain,(
% 1.74/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.74/0.61    inference(cnf_transformation,[],[f5])).
% 1.74/0.61  fof(f5,axiom,(
% 1.74/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.74/0.61  fof(f43,plain,(
% 1.74/0.61    sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.74/0.61    inference(cnf_transformation,[],[f34])).
% 1.74/0.61  fof(f34,plain,(
% 1.74/0.61    ((sK0 != k2_tarski(sK1,sK2) & sK0 != k1_tarski(sK2) & sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))) & (sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)))),
% 1.74/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f33])).
% 1.74/0.61  fof(f33,plain,(
% 1.74/0.61    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)))) => (((sK0 != k2_tarski(sK1,sK2) & sK0 != k1_tarski(sK2) & sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))) & (sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))))),
% 1.74/0.61    introduced(choice_axiom,[])).
% 1.74/0.61  fof(f32,plain,(
% 1.74/0.61    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 1.74/0.61    inference(flattening,[],[f31])).
% 1.74/0.61  fof(f31,plain,(
% 1.74/0.61    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 1.74/0.61    inference(nnf_transformation,[],[f25])).
% 1.74/0.61  fof(f25,plain,(
% 1.74/0.61    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <~> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.74/0.61    inference(ennf_transformation,[],[f21])).
% 1.74/0.61  fof(f21,negated_conjecture,(
% 1.74/0.61    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.74/0.61    inference(negated_conjecture,[],[f20])).
% 1.74/0.61  fof(f20,conjecture,(
% 1.74/0.61    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.74/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).
% 1.74/0.61  fof(f135,plain,(
% 1.74/0.61    ~spl5_6 | ~spl5_7),
% 1.74/0.61    inference(avatar_split_clause,[],[f126,f132,f128])).
% 1.74/0.61  fof(f126,plain,(
% 1.74/0.61    k1_xboole_0 != sK0 | k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))))),
% 1.74/0.61    inference(inner_rewriting,[],[f86])).
% 1.74/0.61  fof(f86,plain,(
% 1.74/0.61    k1_xboole_0 != sK0 | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))))),
% 1.74/0.61    inference(definition_unfolding,[],[f44,f81,f78])).
% 1.74/0.61  fof(f44,plain,(
% 1.74/0.61    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.74/0.61    inference(cnf_transformation,[],[f34])).
% 1.74/0.61  fof(f125,plain,(
% 1.74/0.61    ~spl5_3 | ~spl5_5),
% 1.74/0.61    inference(avatar_split_clause,[],[f85,f122,f113])).
% 1.74/0.61  fof(f85,plain,(
% 1.74/0.61    sK0 != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))))),
% 1.74/0.61    inference(definition_unfolding,[],[f45,f82,f81,f78])).
% 1.74/0.61  fof(f45,plain,(
% 1.74/0.61    sK0 != k1_tarski(sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.74/0.61    inference(cnf_transformation,[],[f34])).
% 1.74/0.61  fof(f120,plain,(
% 1.74/0.61    ~spl5_3 | ~spl5_4),
% 1.74/0.61    inference(avatar_split_clause,[],[f84,f117,f113])).
% 1.74/0.61  fof(f84,plain,(
% 1.74/0.61    sK0 != k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK2) | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))))),
% 1.74/0.61    inference(definition_unfolding,[],[f46,f82,f81,f78])).
% 1.74/0.61  fof(f46,plain,(
% 1.74/0.61    sK0 != k1_tarski(sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.74/0.61    inference(cnf_transformation,[],[f34])).
% 1.74/0.61  fof(f111,plain,(
% 1.74/0.61    ~spl5_1 | ~spl5_2),
% 1.74/0.61    inference(avatar_split_clause,[],[f102,f108,f104])).
% 1.74/0.61  fof(f102,plain,(
% 1.74/0.61    sK0 != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2) | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK0),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.74/0.61    inference(inner_rewriting,[],[f83])).
% 1.74/0.61  fof(f83,plain,(
% 1.74/0.61    sK0 != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2) | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK2)))))),
% 1.74/0.61    inference(definition_unfolding,[],[f47,f78,f81,f78])).
% 1.74/0.61  fof(f47,plain,(
% 1.74/0.61    sK0 != k2_tarski(sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.74/0.61    inference(cnf_transformation,[],[f34])).
% 1.74/0.61  % SZS output end Proof for theBenchmark
% 1.74/0.61  % (1567)------------------------------
% 1.74/0.61  % (1567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.61  % (1567)Termination reason: Refutation
% 1.74/0.61  
% 1.74/0.61  % (1567)Memory used [KB]: 6908
% 1.74/0.61  % (1567)Time elapsed: 0.190 s
% 1.74/0.61  % (1567)------------------------------
% 1.74/0.61  % (1567)------------------------------
% 1.74/0.61  % (1539)Success in time 0.248 s
%------------------------------------------------------------------------------
