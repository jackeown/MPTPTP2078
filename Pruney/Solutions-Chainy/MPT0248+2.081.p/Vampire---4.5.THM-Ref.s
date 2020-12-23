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
% DateTime   : Thu Dec  3 12:38:01 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 884 expanded)
%              Number of leaves         :   35 ( 296 expanded)
%              Depth                    :   19
%              Number of atoms          :  398 (1552 expanded)
%              Number of equality atoms :  163 (1089 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1385,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f136,f143,f1099,f1137,f1152,f1286,f1362,f1378,f1381,f1384])).

fof(f1384,plain,
    ( ~ spl5_1
    | ~ spl5_4
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f1383])).

fof(f1383,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_4
    | spl5_5 ),
    inference(subsumption_resolution,[],[f1382,f142])).

fof(f142,plain,
    ( sK1 != sK2
    | spl5_5 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl5_5
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1382,plain,
    ( sK1 = sK2
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f134,f121])).

fof(f121,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl5_1
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f134,plain,
    ( sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl5_4
  <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1381,plain,
    ( spl5_12
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f1106,f133,f1101])).

fof(f1101,plain,
    ( spl5_12
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f1106,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f366,f134])).

fof(f366,plain,(
    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f104,f101])).

fof(f101,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f50,f96,f94])).

fof(f94,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f93])).

fof(f93,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f78,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f83,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f85,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f86,f87])).

fof(f87,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f83,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f78,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f63,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f96,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f93])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f50,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f104,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f60,f94])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1378,plain,
    ( spl5_12
    | ~ spl5_1
    | spl5_6 ),
    inference(avatar_split_clause,[],[f1353,f1043,f120,f1101])).

fof(f1043,plain,
    ( spl5_6
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f1353,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_1
    | spl5_6 ),
    inference(resolution,[],[f1302,f1339])).

fof(f1339,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_1
    | spl5_6 ),
    inference(resolution,[],[f1293,f1044])).

fof(f1044,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f1043])).

fof(f1293,plain,
    ( ! [X1] :
        ( r1_xboole_0(sK1,X1)
        | r2_hidden(sK0,X1) )
    | ~ spl5_1 ),
    inference(superposition,[],[f105,f121])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f68,f96])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f1302,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK0,X2)
        | r1_tarski(sK1,X2) )
    | ~ spl5_1 ),
    inference(duplicate_literal_removal,[],[f1297])).

fof(f1297,plain,
    ( ! [X2] :
        ( r1_tarski(sK1,X2)
        | ~ r2_hidden(sK0,X2)
        | ~ r2_hidden(sK0,X2) )
    | ~ spl5_1 ),
    inference(superposition,[],[f112,f121])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f82,f93])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f1362,plain,
    ( ~ spl5_6
    | ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f1361,f124,f120,f1043])).

fof(f124,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1361,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f1360,f126])).

fof(f126,plain,
    ( k1_xboole_0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f1360,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f1321,f516])).

fof(f516,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(backward_demodulation,[],[f186,f514])).

fof(f514,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f513,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f513,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f102,f103])).

fof(f103,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f59,f94])).

fof(f59,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f102,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f58,f95])).

fof(f95,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f64,f94])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f58,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f186,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X1,k5_xboole_0(X2,X1)) ),
    inference(superposition,[],[f170,f61])).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f170,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f79,f54])).

fof(f79,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1321,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl5_1 ),
    inference(superposition,[],[f651,f1289])).

fof(f1289,plain,
    ( sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f101,f121])).

fof(f651,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f108,f79])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f73,f95])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f1286,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f1283,f129,f120])).

fof(f129,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1283,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f1276,f131])).

fof(f131,plain,
    ( k1_xboole_0 != sK1
    | spl5_3 ),
    inference(avatar_component_clause,[],[f129])).

fof(f1276,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f111,f366])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f75,f96,f96])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f1152,plain,(
    ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f1144])).

fof(f1144,plain,
    ( $false
    | ~ spl5_8 ),
    inference(resolution,[],[f1083,f146])).

fof(f146,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f72,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1083,plain,
    ( ! [X9] : ~ r1_tarski(X9,k1_xboole_0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f1082])).

fof(f1082,plain,
    ( spl5_8
  <=> ! [X9] : ~ r1_tarski(X9,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f1137,plain,
    ( ~ spl5_12
    | spl5_4 ),
    inference(avatar_split_clause,[],[f498,f133,f1101])).

fof(f498,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_4 ),
    inference(subsumption_resolution,[],[f495,f135])).

fof(f135,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f133])).

fof(f495,plain,
    ( sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ r1_tarski(sK1,sK2) ),
    inference(superposition,[],[f106,f101])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f69,f94])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1099,plain,
    ( spl5_8
    | ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f1080,f133,f129,f1082])).

fof(f1080,plain,
    ( ! [X15] :
        ( k1_xboole_0 != sK1
        | ~ r1_tarski(X15,k1_xboole_0) )
    | spl5_4 ),
    inference(resolution,[],[f1061,f500])).

fof(f500,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ r1_tarski(X0,k1_xboole_0) )
    | spl5_4 ),
    inference(resolution,[],[f498,f280])).

fof(f280,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(X7,X8)
      | ~ r1_tarski(X7,X6)
      | ~ r1_tarski(X6,k1_xboole_0) ) ),
    inference(resolution,[],[f163,f71])).

fof(f163,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X7,X8)
      | ~ r1_tarski(X6,k1_xboole_0)
      | ~ r1_tarski(X8,X6) ) ),
    inference(resolution,[],[f156,f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f156,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ r1_tarski(X4,k1_xboole_0) ) ),
    inference(resolution,[],[f70,f148])).

fof(f148,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f67,f116])).

fof(f116,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
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

fof(f1061,plain,(
    ! [X4,X5] :
      ( r1_tarski(X4,X5)
      | k1_xboole_0 != X4 ) ),
    inference(resolution,[],[f1058,f71])).

fof(f1058,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,X1)
      | k1_xboole_0 != X1 ) ),
    inference(duplicate_literal_removal,[],[f1057])).

fof(f1057,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f1051,f67])).

fof(f1051,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(forward_demodulation,[],[f1031,f515])).

fof(f515,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f170,f514])).

fof(f1031,plain,(
    ! [X0] :
      ( k1_xboole_0 != k5_xboole_0(X0,k5_xboole_0(X0,X0))
      | r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f607,f103])).

fof(f607,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))
      | r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f107,f79])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f74,f95])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f143,plain,
    ( ~ spl5_5
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f138,f120,f140])).

fof(f138,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f137])).

fof(f137,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f100])).

fof(f100,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f51,f96,f96])).

fof(f51,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f136,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f99,f133,f129])).

fof(f99,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f52,f96])).

fof(f52,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f38])).

fof(f127,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f98,f124,f120])).

fof(f98,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f53,f96])).

fof(f53,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:45:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.46  % (23801)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (23818)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.50  % (23791)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (23800)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.29/0.51  % (23800)Refutation not found, incomplete strategy% (23800)------------------------------
% 1.29/0.51  % (23800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.51  % (23800)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.51  
% 1.29/0.51  % (23800)Memory used [KB]: 10618
% 1.29/0.51  % (23800)Time elapsed: 0.108 s
% 1.29/0.51  % (23800)------------------------------
% 1.29/0.51  % (23800)------------------------------
% 1.29/0.51  % (23790)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.51  % (23802)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.51  % (23799)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.29/0.52  % (23795)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.52  % (23793)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.52  % (23811)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.29/0.52  % (23811)Refutation not found, incomplete strategy% (23811)------------------------------
% 1.29/0.52  % (23811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.52  % (23811)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.52  
% 1.29/0.52  % (23811)Memory used [KB]: 10874
% 1.29/0.52  % (23811)Time elapsed: 0.086 s
% 1.29/0.52  % (23811)------------------------------
% 1.29/0.52  % (23811)------------------------------
% 1.29/0.53  % (23797)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.53  % (23803)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.38/0.53  % (23805)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.53  % (23813)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.53  % (23794)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.38/0.53  % (23792)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.53  % (23799)Refutation not found, incomplete strategy% (23799)------------------------------
% 1.38/0.53  % (23799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (23799)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (23799)Memory used [KB]: 10618
% 1.38/0.53  % (23799)Time elapsed: 0.106 s
% 1.38/0.53  % (23799)------------------------------
% 1.38/0.53  % (23799)------------------------------
% 1.38/0.53  % (23789)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.38/0.53  % (23807)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.53  % (23810)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.53  % (23816)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.53  % (23808)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.54  % (23798)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.38/0.54  % (23817)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.54  % (23809)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.54  % (23815)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.54  % (23810)Refutation not found, incomplete strategy% (23810)------------------------------
% 1.38/0.54  % (23810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (23810)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (23810)Memory used [KB]: 1791
% 1.38/0.54  % (23810)Time elapsed: 0.110 s
% 1.38/0.54  % (23810)------------------------------
% 1.38/0.54  % (23810)------------------------------
% 1.38/0.54  % (23814)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.55  % (23806)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.55  % (23804)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.55  % (23812)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.55  % (23804)Refutation not found, incomplete strategy% (23804)------------------------------
% 1.38/0.55  % (23804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (23806)Refutation not found, incomplete strategy% (23806)------------------------------
% 1.38/0.55  % (23806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (23796)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.56  % (23806)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  % (23804)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (23804)Memory used [KB]: 6140
% 1.38/0.56  % (23804)Time elapsed: 0.004 s
% 1.38/0.56  % (23804)------------------------------
% 1.38/0.56  % (23804)------------------------------
% 1.38/0.56  
% 1.38/0.56  % (23806)Memory used [KB]: 10618
% 1.38/0.56  % (23806)Time elapsed: 0.153 s
% 1.38/0.56  % (23806)------------------------------
% 1.38/0.56  % (23806)------------------------------
% 1.38/0.60  % (23816)Refutation found. Thanks to Tanya!
% 1.38/0.60  % SZS status Theorem for theBenchmark
% 2.05/0.63  % SZS output start Proof for theBenchmark
% 2.05/0.63  fof(f1385,plain,(
% 2.05/0.63    $false),
% 2.05/0.63    inference(avatar_sat_refutation,[],[f127,f136,f143,f1099,f1137,f1152,f1286,f1362,f1378,f1381,f1384])).
% 2.05/0.63  fof(f1384,plain,(
% 2.05/0.63    ~spl5_1 | ~spl5_4 | spl5_5),
% 2.05/0.63    inference(avatar_contradiction_clause,[],[f1383])).
% 2.05/0.63  fof(f1383,plain,(
% 2.05/0.63    $false | (~spl5_1 | ~spl5_4 | spl5_5)),
% 2.05/0.63    inference(subsumption_resolution,[],[f1382,f142])).
% 2.05/0.63  fof(f142,plain,(
% 2.05/0.63    sK1 != sK2 | spl5_5),
% 2.05/0.63    inference(avatar_component_clause,[],[f140])).
% 2.05/0.63  fof(f140,plain,(
% 2.05/0.63    spl5_5 <=> sK1 = sK2),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.05/0.63  fof(f1382,plain,(
% 2.05/0.63    sK1 = sK2 | (~spl5_1 | ~spl5_4)),
% 2.05/0.63    inference(forward_demodulation,[],[f134,f121])).
% 2.05/0.63  fof(f121,plain,(
% 2.05/0.63    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl5_1),
% 2.05/0.63    inference(avatar_component_clause,[],[f120])).
% 2.05/0.63  fof(f120,plain,(
% 2.05/0.63    spl5_1 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.05/0.63  fof(f134,plain,(
% 2.05/0.63    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl5_4),
% 2.05/0.63    inference(avatar_component_clause,[],[f133])).
% 2.05/0.63  fof(f133,plain,(
% 2.05/0.63    spl5_4 <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.05/0.63  fof(f1381,plain,(
% 2.05/0.63    spl5_12 | ~spl5_4),
% 2.05/0.63    inference(avatar_split_clause,[],[f1106,f133,f1101])).
% 2.05/0.63  fof(f1101,plain,(
% 2.05/0.63    spl5_12 <=> r1_tarski(sK1,sK2)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.05/0.63  fof(f1106,plain,(
% 2.05/0.63    r1_tarski(sK1,sK2) | ~spl5_4),
% 2.05/0.63    inference(backward_demodulation,[],[f366,f134])).
% 2.05/0.63  fof(f366,plain,(
% 2.05/0.63    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.05/0.63    inference(superposition,[],[f104,f101])).
% 2.05/0.63  fof(f101,plain,(
% 2.05/0.63    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.05/0.63    inference(definition_unfolding,[],[f50,f96,f94])).
% 2.05/0.63  fof(f94,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.05/0.63    inference(definition_unfolding,[],[f62,f93])).
% 2.05/0.63  fof(f93,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.05/0.63    inference(definition_unfolding,[],[f63,f92])).
% 2.05/0.63  fof(f92,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.05/0.63    inference(definition_unfolding,[],[f78,f91])).
% 2.05/0.63  fof(f91,plain,(
% 2.05/0.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.05/0.63    inference(definition_unfolding,[],[f83,f90])).
% 2.05/0.63  fof(f90,plain,(
% 2.05/0.63    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.05/0.63    inference(definition_unfolding,[],[f85,f89])).
% 2.05/0.63  fof(f89,plain,(
% 2.05/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.05/0.63    inference(definition_unfolding,[],[f86,f87])).
% 2.05/0.63  fof(f87,plain,(
% 2.05/0.63    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f21])).
% 2.05/0.63  fof(f21,axiom,(
% 2.05/0.63    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.05/0.63  fof(f86,plain,(
% 2.05/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f20])).
% 2.05/0.63  fof(f20,axiom,(
% 2.05/0.63    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.05/0.63  fof(f85,plain,(
% 2.05/0.63    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f19])).
% 2.05/0.63  fof(f19,axiom,(
% 2.05/0.63    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.05/0.63  fof(f83,plain,(
% 2.05/0.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f18])).
% 2.05/0.63  fof(f18,axiom,(
% 2.05/0.63    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.05/0.63  fof(f78,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f17])).
% 2.05/0.63  fof(f17,axiom,(
% 2.05/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.05/0.63  fof(f63,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f16])).
% 2.05/0.63  fof(f16,axiom,(
% 2.05/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.05/0.63  fof(f62,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f24])).
% 2.05/0.63  fof(f24,axiom,(
% 2.05/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.05/0.63  fof(f96,plain,(
% 2.05/0.63    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.05/0.63    inference(definition_unfolding,[],[f55,f93])).
% 2.05/0.63  fof(f55,plain,(
% 2.05/0.63    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f15])).
% 2.05/0.63  fof(f15,axiom,(
% 2.05/0.63    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.05/0.63  fof(f50,plain,(
% 2.05/0.63    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.05/0.63    inference(cnf_transformation,[],[f38])).
% 2.05/0.63  fof(f38,plain,(
% 2.05/0.63    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.05/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f37])).
% 2.05/0.63  fof(f37,plain,(
% 2.05/0.63    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 2.05/0.63    introduced(choice_axiom,[])).
% 2.05/0.63  fof(f31,plain,(
% 2.05/0.63    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.05/0.63    inference(ennf_transformation,[],[f27])).
% 2.05/0.63  fof(f27,negated_conjecture,(
% 2.05/0.63    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.05/0.63    inference(negated_conjecture,[],[f26])).
% 2.05/0.63  fof(f26,conjecture,(
% 2.05/0.63    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.05/0.63  fof(f104,plain,(
% 2.05/0.63    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.05/0.63    inference(definition_unfolding,[],[f60,f94])).
% 2.05/0.63  fof(f60,plain,(
% 2.05/0.63    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f9])).
% 2.05/0.63  fof(f9,axiom,(
% 2.05/0.63    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.05/0.63  fof(f1378,plain,(
% 2.05/0.63    spl5_12 | ~spl5_1 | spl5_6),
% 2.05/0.63    inference(avatar_split_clause,[],[f1353,f1043,f120,f1101])).
% 2.05/0.63  fof(f1043,plain,(
% 2.05/0.63    spl5_6 <=> r1_xboole_0(sK1,sK2)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.05/0.63  fof(f1353,plain,(
% 2.05/0.63    r1_tarski(sK1,sK2) | (~spl5_1 | spl5_6)),
% 2.05/0.63    inference(resolution,[],[f1302,f1339])).
% 2.05/0.63  fof(f1339,plain,(
% 2.05/0.63    r2_hidden(sK0,sK2) | (~spl5_1 | spl5_6)),
% 2.05/0.63    inference(resolution,[],[f1293,f1044])).
% 2.05/0.63  fof(f1044,plain,(
% 2.05/0.63    ~r1_xboole_0(sK1,sK2) | spl5_6),
% 2.05/0.63    inference(avatar_component_clause,[],[f1043])).
% 2.05/0.63  fof(f1293,plain,(
% 2.05/0.63    ( ! [X1] : (r1_xboole_0(sK1,X1) | r2_hidden(sK0,X1)) ) | ~spl5_1),
% 2.05/0.63    inference(superposition,[],[f105,f121])).
% 2.05/0.63  fof(f105,plain,(
% 2.05/0.63    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.05/0.63    inference(definition_unfolding,[],[f68,f96])).
% 2.05/0.63  fof(f68,plain,(
% 2.05/0.63    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f34])).
% 2.05/0.63  fof(f34,plain,(
% 2.05/0.63    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.05/0.63    inference(ennf_transformation,[],[f22])).
% 2.05/0.63  fof(f22,axiom,(
% 2.05/0.63    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.05/0.63  fof(f1302,plain,(
% 2.05/0.63    ( ! [X2] : (~r2_hidden(sK0,X2) | r1_tarski(sK1,X2)) ) | ~spl5_1),
% 2.05/0.63    inference(duplicate_literal_removal,[],[f1297])).
% 2.05/0.63  fof(f1297,plain,(
% 2.05/0.63    ( ! [X2] : (r1_tarski(sK1,X2) | ~r2_hidden(sK0,X2) | ~r2_hidden(sK0,X2)) ) | ~spl5_1),
% 2.05/0.63    inference(superposition,[],[f112,f121])).
% 2.05/0.63  fof(f112,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.05/0.63    inference(definition_unfolding,[],[f82,f93])).
% 2.05/0.63  fof(f82,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f49])).
% 2.05/0.63  fof(f49,plain,(
% 2.05/0.63    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.05/0.63    inference(flattening,[],[f48])).
% 2.05/0.63  fof(f48,plain,(
% 2.05/0.63    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.05/0.63    inference(nnf_transformation,[],[f25])).
% 2.05/0.63  fof(f25,axiom,(
% 2.05/0.63    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 2.05/0.63  fof(f1362,plain,(
% 2.05/0.63    ~spl5_6 | ~spl5_1 | spl5_2),
% 2.05/0.63    inference(avatar_split_clause,[],[f1361,f124,f120,f1043])).
% 2.05/0.63  fof(f124,plain,(
% 2.05/0.63    spl5_2 <=> k1_xboole_0 = sK2),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.05/0.63  fof(f1361,plain,(
% 2.05/0.63    ~r1_xboole_0(sK1,sK2) | (~spl5_1 | spl5_2)),
% 2.05/0.63    inference(subsumption_resolution,[],[f1360,f126])).
% 2.05/0.63  fof(f126,plain,(
% 2.05/0.63    k1_xboole_0 != sK2 | spl5_2),
% 2.05/0.63    inference(avatar_component_clause,[],[f124])).
% 2.05/0.63  fof(f1360,plain,(
% 2.05/0.63    k1_xboole_0 = sK2 | ~r1_xboole_0(sK1,sK2) | ~spl5_1),
% 2.05/0.63    inference(forward_demodulation,[],[f1321,f516])).
% 2.05/0.63  fof(f516,plain,(
% 2.05/0.63    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 2.05/0.63    inference(backward_demodulation,[],[f186,f514])).
% 2.05/0.63  fof(f514,plain,(
% 2.05/0.63    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.05/0.63    inference(forward_demodulation,[],[f513,f54])).
% 2.05/0.63  fof(f54,plain,(
% 2.05/0.63    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f11])).
% 2.05/0.63  fof(f11,axiom,(
% 2.05/0.63    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.05/0.63  fof(f513,plain,(
% 2.05/0.63    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 2.05/0.63    inference(forward_demodulation,[],[f102,f103])).
% 2.05/0.63  fof(f103,plain,(
% 2.05/0.63    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.05/0.63    inference(definition_unfolding,[],[f59,f94])).
% 2.05/0.63  fof(f59,plain,(
% 2.05/0.63    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.05/0.63    inference(cnf_transformation,[],[f29])).
% 2.05/0.63  fof(f29,plain,(
% 2.05/0.63    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.05/0.63    inference(rectify,[],[f4])).
% 2.05/0.63  fof(f4,axiom,(
% 2.05/0.63    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.05/0.63  fof(f102,plain,(
% 2.05/0.63    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 2.05/0.63    inference(definition_unfolding,[],[f58,f95])).
% 2.05/0.63  fof(f95,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.05/0.63    inference(definition_unfolding,[],[f64,f94])).
% 2.05/0.63  fof(f64,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f12])).
% 2.05/0.63  fof(f12,axiom,(
% 2.05/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.05/0.63  fof(f58,plain,(
% 2.05/0.63    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.05/0.63    inference(cnf_transformation,[],[f28])).
% 2.05/0.63  fof(f28,plain,(
% 2.05/0.63    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.05/0.63    inference(rectify,[],[f5])).
% 2.05/0.63  fof(f5,axiom,(
% 2.05/0.63    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.05/0.63  fof(f186,plain,(
% 2.05/0.63    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(X1,k5_xboole_0(X2,X1))) )),
% 2.05/0.63    inference(superposition,[],[f170,f61])).
% 2.05/0.63  fof(f61,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f1])).
% 2.05/0.63  fof(f1,axiom,(
% 2.05/0.63    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.05/0.63  fof(f170,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 2.05/0.63    inference(superposition,[],[f79,f54])).
% 2.05/0.63  fof(f79,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f10])).
% 2.05/0.63  fof(f10,axiom,(
% 2.05/0.63    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.05/0.63  fof(f1321,plain,(
% 2.05/0.63    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)) | ~r1_xboole_0(sK1,sK2) | ~spl5_1),
% 2.05/0.63    inference(superposition,[],[f651,f1289])).
% 2.05/0.63  fof(f1289,plain,(
% 2.05/0.63    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl5_1),
% 2.05/0.63    inference(backward_demodulation,[],[f101,f121])).
% 2.05/0.63  fof(f651,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) | ~r1_xboole_0(X0,X1)) )),
% 2.05/0.63    inference(forward_demodulation,[],[f108,f79])).
% 2.05/0.63  fof(f108,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 2.05/0.63    inference(definition_unfolding,[],[f73,f95])).
% 2.05/0.63  fof(f73,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f45])).
% 2.05/0.63  fof(f45,plain,(
% 2.05/0.63    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.05/0.63    inference(nnf_transformation,[],[f3])).
% 2.05/0.63  fof(f3,axiom,(
% 2.05/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.05/0.63  fof(f1286,plain,(
% 2.05/0.63    spl5_1 | spl5_3),
% 2.05/0.63    inference(avatar_split_clause,[],[f1283,f129,f120])).
% 2.05/0.63  fof(f129,plain,(
% 2.05/0.63    spl5_3 <=> k1_xboole_0 = sK1),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.05/0.63  fof(f1283,plain,(
% 2.05/0.63    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl5_3),
% 2.05/0.63    inference(subsumption_resolution,[],[f1276,f131])).
% 2.05/0.63  fof(f131,plain,(
% 2.05/0.63    k1_xboole_0 != sK1 | spl5_3),
% 2.05/0.63    inference(avatar_component_clause,[],[f129])).
% 2.05/0.63  fof(f1276,plain,(
% 2.05/0.63    k1_xboole_0 = sK1 | sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.05/0.63    inference(resolution,[],[f111,f366])).
% 2.05/0.63  fof(f111,plain,(
% 2.05/0.63    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 2.05/0.63    inference(definition_unfolding,[],[f75,f96,f96])).
% 2.05/0.63  fof(f75,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f47])).
% 2.05/0.63  fof(f47,plain,(
% 2.05/0.63    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.05/0.63    inference(flattening,[],[f46])).
% 2.05/0.63  fof(f46,plain,(
% 2.05/0.63    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.05/0.63    inference(nnf_transformation,[],[f23])).
% 2.05/0.63  fof(f23,axiom,(
% 2.05/0.63    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.05/0.63  fof(f1152,plain,(
% 2.05/0.63    ~spl5_8),
% 2.05/0.63    inference(avatar_contradiction_clause,[],[f1144])).
% 2.05/0.63  fof(f1144,plain,(
% 2.05/0.63    $false | ~spl5_8),
% 2.05/0.63    inference(resolution,[],[f1083,f146])).
% 2.05/0.63  fof(f146,plain,(
% 2.05/0.63    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.05/0.63    inference(duplicate_literal_removal,[],[f145])).
% 2.05/0.63  fof(f145,plain,(
% 2.05/0.63    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 2.05/0.63    inference(resolution,[],[f72,f71])).
% 2.05/0.63  fof(f71,plain,(
% 2.05/0.63    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f44])).
% 2.05/0.63  fof(f44,plain,(
% 2.05/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.05/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).
% 2.05/0.63  fof(f43,plain,(
% 2.05/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.05/0.63    introduced(choice_axiom,[])).
% 2.05/0.63  fof(f42,plain,(
% 2.05/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.05/0.63    inference(rectify,[],[f41])).
% 2.05/0.63  fof(f41,plain,(
% 2.05/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.05/0.63    inference(nnf_transformation,[],[f36])).
% 2.05/0.63  fof(f36,plain,(
% 2.05/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.05/0.63    inference(ennf_transformation,[],[f2])).
% 2.05/0.63  fof(f2,axiom,(
% 2.05/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.05/0.63  fof(f72,plain,(
% 2.05/0.63    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f44])).
% 2.05/0.63  fof(f1083,plain,(
% 2.05/0.63    ( ! [X9] : (~r1_tarski(X9,k1_xboole_0)) ) | ~spl5_8),
% 2.05/0.63    inference(avatar_component_clause,[],[f1082])).
% 2.05/0.63  fof(f1082,plain,(
% 2.05/0.63    spl5_8 <=> ! [X9] : ~r1_tarski(X9,k1_xboole_0)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 2.05/0.63  fof(f1137,plain,(
% 2.05/0.63    ~spl5_12 | spl5_4),
% 2.05/0.63    inference(avatar_split_clause,[],[f498,f133,f1101])).
% 2.05/0.63  fof(f498,plain,(
% 2.05/0.63    ~r1_tarski(sK1,sK2) | spl5_4),
% 2.05/0.63    inference(subsumption_resolution,[],[f495,f135])).
% 2.05/0.63  fof(f135,plain,(
% 2.05/0.63    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl5_4),
% 2.05/0.63    inference(avatar_component_clause,[],[f133])).
% 2.05/0.63  fof(f495,plain,(
% 2.05/0.63    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~r1_tarski(sK1,sK2)),
% 2.05/0.63    inference(superposition,[],[f106,f101])).
% 2.05/0.63  fof(f106,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.05/0.63    inference(definition_unfolding,[],[f69,f94])).
% 2.05/0.63  fof(f69,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f35])).
% 2.05/0.63  fof(f35,plain,(
% 2.05/0.63    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.05/0.63    inference(ennf_transformation,[],[f7])).
% 2.05/0.63  fof(f7,axiom,(
% 2.05/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.05/0.63  fof(f1099,plain,(
% 2.05/0.63    spl5_8 | ~spl5_3 | spl5_4),
% 2.05/0.63    inference(avatar_split_clause,[],[f1080,f133,f129,f1082])).
% 2.05/0.63  fof(f1080,plain,(
% 2.05/0.63    ( ! [X15] : (k1_xboole_0 != sK1 | ~r1_tarski(X15,k1_xboole_0)) ) | spl5_4),
% 2.05/0.63    inference(resolution,[],[f1061,f500])).
% 2.05/0.63  fof(f500,plain,(
% 2.05/0.63    ( ! [X0] : (~r1_tarski(sK1,X0) | ~r1_tarski(X0,k1_xboole_0)) ) | spl5_4),
% 2.05/0.63    inference(resolution,[],[f498,f280])).
% 2.05/0.63  fof(f280,plain,(
% 2.05/0.63    ( ! [X6,X8,X7] : (r1_tarski(X7,X8) | ~r1_tarski(X7,X6) | ~r1_tarski(X6,k1_xboole_0)) )),
% 2.05/0.63    inference(resolution,[],[f163,f71])).
% 2.05/0.63  fof(f163,plain,(
% 2.05/0.63    ( ! [X6,X8,X7] : (~r2_hidden(X7,X8) | ~r1_tarski(X6,k1_xboole_0) | ~r1_tarski(X8,X6)) )),
% 2.05/0.63    inference(resolution,[],[f156,f70])).
% 2.05/0.63  fof(f70,plain,(
% 2.05/0.63    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f44])).
% 2.05/0.63  fof(f156,plain,(
% 2.05/0.63    ( ! [X4,X3] : (~r2_hidden(X3,X4) | ~r1_tarski(X4,k1_xboole_0)) )),
% 2.05/0.63    inference(resolution,[],[f70,f148])).
% 2.05/0.63  fof(f148,plain,(
% 2.05/0.63    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.05/0.63    inference(duplicate_literal_removal,[],[f147])).
% 2.05/0.63  fof(f147,plain,(
% 2.05/0.63    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 2.05/0.63    inference(resolution,[],[f67,f116])).
% 2.05/0.63  fof(f116,plain,(
% 2.05/0.63    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.05/0.63    inference(equality_resolution,[],[f56])).
% 2.05/0.63  fof(f56,plain,(
% 2.05/0.63    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f32])).
% 2.05/0.63  fof(f32,plain,(
% 2.05/0.63    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 2.05/0.63    inference(ennf_transformation,[],[f8])).
% 2.05/0.63  fof(f8,axiom,(
% 2.05/0.63    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 2.05/0.63  fof(f67,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f40])).
% 2.05/0.63  fof(f40,plain,(
% 2.05/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.05/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f39])).
% 2.05/0.63  fof(f39,plain,(
% 2.05/0.63    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 2.05/0.63    introduced(choice_axiom,[])).
% 2.05/0.63  fof(f33,plain,(
% 2.05/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.05/0.63    inference(ennf_transformation,[],[f30])).
% 2.05/0.63  fof(f30,plain,(
% 2.05/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.05/0.63    inference(rectify,[],[f6])).
% 2.05/0.63  fof(f6,axiom,(
% 2.05/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.05/0.63  fof(f1061,plain,(
% 2.05/0.63    ( ! [X4,X5] : (r1_tarski(X4,X5) | k1_xboole_0 != X4) )),
% 2.05/0.63    inference(resolution,[],[f1058,f71])).
% 2.05/0.63  fof(f1058,plain,(
% 2.05/0.63    ( ! [X2,X1] : (~r2_hidden(X2,X1) | k1_xboole_0 != X1) )),
% 2.05/0.63    inference(duplicate_literal_removal,[],[f1057])).
% 2.05/0.63  fof(f1057,plain,(
% 2.05/0.63    ( ! [X2,X1] : (k1_xboole_0 != X1 | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X1)) )),
% 2.05/0.63    inference(resolution,[],[f1051,f67])).
% 2.05/0.63  fof(f1051,plain,(
% 2.05/0.63    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 2.05/0.63    inference(forward_demodulation,[],[f1031,f515])).
% 2.05/0.63  fof(f515,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.05/0.63    inference(backward_demodulation,[],[f170,f514])).
% 2.05/0.63  fof(f1031,plain,(
% 2.05/0.63    ( ! [X0] : (k1_xboole_0 != k5_xboole_0(X0,k5_xboole_0(X0,X0)) | r1_xboole_0(X0,X0)) )),
% 2.05/0.63    inference(superposition,[],[f607,f103])).
% 2.05/0.63  fof(f607,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) | r1_xboole_0(X0,X1)) )),
% 2.05/0.63    inference(forward_demodulation,[],[f107,f79])).
% 2.05/0.63  fof(f107,plain,(
% 2.05/0.63    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.05/0.63    inference(definition_unfolding,[],[f74,f95])).
% 2.05/0.63  fof(f74,plain,(
% 2.05/0.63    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.05/0.63    inference(cnf_transformation,[],[f45])).
% 2.05/0.63  fof(f143,plain,(
% 2.05/0.63    ~spl5_5 | ~spl5_1),
% 2.05/0.63    inference(avatar_split_clause,[],[f138,f120,f140])).
% 2.05/0.63  fof(f138,plain,(
% 2.05/0.63    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != sK2),
% 2.05/0.63    inference(inner_rewriting,[],[f137])).
% 2.05/0.63  fof(f137,plain,(
% 2.05/0.63    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != sK2),
% 2.05/0.63    inference(inner_rewriting,[],[f100])).
% 2.05/0.63  fof(f100,plain,(
% 2.05/0.63    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.05/0.63    inference(definition_unfolding,[],[f51,f96,f96])).
% 2.05/0.63  fof(f51,plain,(
% 2.05/0.63    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 2.05/0.63    inference(cnf_transformation,[],[f38])).
% 2.05/0.63  fof(f136,plain,(
% 2.05/0.63    ~spl5_3 | ~spl5_4),
% 2.05/0.63    inference(avatar_split_clause,[],[f99,f133,f129])).
% 2.05/0.63  fof(f99,plain,(
% 2.05/0.63    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 2.05/0.63    inference(definition_unfolding,[],[f52,f96])).
% 2.05/0.63  fof(f52,plain,(
% 2.05/0.63    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 2.05/0.63    inference(cnf_transformation,[],[f38])).
% 2.05/0.63  fof(f127,plain,(
% 2.05/0.63    ~spl5_1 | ~spl5_2),
% 2.05/0.63    inference(avatar_split_clause,[],[f98,f124,f120])).
% 2.05/0.63  fof(f98,plain,(
% 2.05/0.63    k1_xboole_0 != sK2 | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.05/0.63    inference(definition_unfolding,[],[f53,f96])).
% 2.05/0.63  fof(f53,plain,(
% 2.05/0.63    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 2.05/0.63    inference(cnf_transformation,[],[f38])).
% 2.05/0.63  % SZS output end Proof for theBenchmark
% 2.05/0.63  % (23816)------------------------------
% 2.05/0.63  % (23816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.63  % (23816)Termination reason: Refutation
% 2.05/0.63  
% 2.05/0.63  % (23816)Memory used [KB]: 6908
% 2.05/0.63  % (23816)Time elapsed: 0.211 s
% 2.05/0.63  % (23816)------------------------------
% 2.05/0.63  % (23816)------------------------------
% 2.05/0.64  % (23788)Success in time 0.281 s
%------------------------------------------------------------------------------
