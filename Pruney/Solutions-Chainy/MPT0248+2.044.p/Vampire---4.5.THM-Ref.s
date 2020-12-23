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
% DateTime   : Thu Dec  3 12:37:55 EST 2020

% Result     : Theorem 2.45s
% Output     : Refutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 718 expanded)
%              Number of leaves         :   40 ( 247 expanded)
%              Depth                    :   21
%              Number of atoms          :  404 (1420 expanded)
%              Number of equality atoms :  170 ( 727 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2844,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f122,f128,f132,f144,f207,f382,f386,f392,f1018,f1164,f1319,f1380,f1581,f2837,f2841])).

fof(f2841,plain,
    ( sK1 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK2 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2837,plain,
    ( spl5_2
    | ~ spl5_46
    | ~ spl5_49 ),
    inference(avatar_split_clause,[],[f2835,f1573,f1378,f113])).

fof(f113,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1378,plain,
    ( spl5_46
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f1573,plain,
    ( spl5_49
  <=> sK1 = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f2835,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_46
    | ~ spl5_49 ),
    inference(forward_demodulation,[],[f2816,f1379])).

fof(f1379,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f1378])).

fof(f2816,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl5_49 ),
    inference(superposition,[],[f202,f1574])).

fof(f1574,plain,
    ( sK1 = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1))
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f1573])).

fof(f202,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X4))) = X3 ),
    inference(resolution,[],[f96,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f96,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f54,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f57,f85])).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f77,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f79,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f80,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f77,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1581,plain,
    ( spl5_49
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_43
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f1580,f1378,f1317,f142,f130,f110,f1573])).

fof(f110,plain,
    ( spl5_1
  <=> sK1 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f130,plain,
    ( spl5_6
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f142,plain,
    ( spl5_7
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f1317,plain,
    ( spl5_43
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f1580,plain,
    ( sK1 = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1))
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_43
    | ~ spl5_46 ),
    inference(forward_demodulation,[],[f1579,f1017])).

fof(f1017,plain,
    ( sK1 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f1579,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1))
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_43
    | ~ spl5_46 ),
    inference(forward_demodulation,[],[f1578,f131])).

fof(f131,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f1578,plain,
    ( k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1))
    | ~ spl5_7
    | ~ spl5_43
    | ~ spl5_46 ),
    inference(forward_demodulation,[],[f1577,f906])).

fof(f906,plain,
    ( ! [X5] : k4_xboole_0(X5,k1_xboole_0) = X5
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f894,f95])).

fof(f95,plain,(
    ! [X0] : k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)),k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f52,f87])).

fof(f87,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f60,f86])).

fof(f60,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f894,plain,
    ( ! [X5] : k4_xboole_0(X5,k1_xboole_0) = k4_xboole_0(k3_tarski(k5_enumset1(X5,X5,X5,X5,X5,X5,k1_xboole_0)),k3_xboole_0(X5,k1_xboole_0))
    | ~ spl5_7 ),
    inference(superposition,[],[f89,f151])).

fof(f151,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)
    | ~ spl5_7 ),
    inference(superposition,[],[f150,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f150,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)
    | ~ spl5_7 ),
    inference(resolution,[],[f148,f65])).

fof(f148,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl5_7 ),
    inference(resolution,[],[f147,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f147,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f146,f137])).

fof(f137,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f136,f65])).

fof(f136,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f70,f69])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f146,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl5_7 ),
    inference(resolution,[],[f143,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f143,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f142])).

fof(f89,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f59,f87])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1577,plain,
    ( k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k1_xboole_0)
    | ~ spl5_7
    | ~ spl5_43
    | ~ spl5_46 ),
    inference(forward_demodulation,[],[f1576,f1318])).

fof(f1318,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f1317])).

fof(f1576,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(sK1,sK2)) = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1))
    | ~ spl5_7
    | ~ spl5_46 ),
    inference(forward_demodulation,[],[f1527,f906])).

fof(f1527,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(sK1,sK2)) = k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)),k1_xboole_0)
    | ~ spl5_46 ),
    inference(superposition,[],[f97,f1379])).

fof(f97,plain,(
    ! [X0,X1] : k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)) = k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)),k3_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f56,f87,f87])).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1380,plain,
    ( spl5_46
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f1349,f1317,f1378])).

fof(f1349,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl5_43 ),
    inference(trivial_inequality_removal,[],[f1339])).

fof(f1339,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl5_43 ),
    inference(superposition,[],[f169,f1318])).

fof(f169,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | k3_xboole_0(X1,X0) = k1_xboole_0 ) ),
    inference(resolution,[],[f133,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f133,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X1,X0) != k1_xboole_0 ) ),
    inference(superposition,[],[f67,f55])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1319,plain,
    ( spl5_43
    | ~ spl5_1
    | spl5_42 ),
    inference(avatar_split_clause,[],[f1311,f1162,f110,f1317])).

fof(f1162,plain,
    ( spl5_42
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f1311,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl5_1
    | spl5_42 ),
    inference(resolution,[],[f1149,f1163])).

fof(f1163,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_42 ),
    inference(avatar_component_clause,[],[f1162])).

fof(f1149,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,X0)
        | k1_xboole_0 = k3_xboole_0(sK1,X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f1082,f66])).

fof(f1082,plain,
    ( ! [X69] :
        ( r1_xboole_0(sK1,X69)
        | r2_hidden(sK0,X69) )
    | ~ spl5_1 ),
    inference(superposition,[],[f98,f1017])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f88])).

fof(f88,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f85])).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f1164,plain,
    ( ~ spl5_42
    | ~ spl5_1
    | spl5_19 ),
    inference(avatar_split_clause,[],[f1156,f389,f110,f1162])).

fof(f389,plain,
    ( spl5_19
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f1156,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl5_1
    | spl5_19 ),
    inference(resolution,[],[f1084,f390])).

fof(f390,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_19 ),
    inference(avatar_component_clause,[],[f389])).

fof(f1084,plain,
    ( ! [X71] :
        ( r1_tarski(sK1,X71)
        | ~ r2_hidden(sK0,X71) )
    | ~ spl5_1 ),
    inference(superposition,[],[f103,f1017])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f75,f88])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f1018,plain,
    ( spl5_1
    | spl5_3
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f1009,f205,f117,f110])).

fof(f117,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f205,plain,
    ( spl5_8
  <=> r1_tarski(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f1009,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_8 ),
    inference(resolution,[],[f102,f206])).

fof(f206,plain,
    ( r1_tarski(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f205])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f71,f88,f88])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f392,plain,
    ( ~ spl5_19
    | spl5_4
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f369,f130,f120,f389])).

fof(f120,plain,
    ( spl5_4
  <=> sK2 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f369,plain,
    ( sK2 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ r1_tarski(sK1,sK2)
    | ~ spl5_6 ),
    inference(superposition,[],[f99,f131])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f86])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f386,plain,(
    spl5_18 ),
    inference(avatar_contradiction_clause,[],[f385])).

fof(f385,plain,
    ( $false
    | spl5_18 ),
    inference(trivial_inequality_removal,[],[f384])).

fof(f384,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl5_18 ),
    inference(resolution,[],[f379,f190])).

fof(f190,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(resolution,[],[f185,f69])).

fof(f185,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,X6)
      | k1_xboole_0 != X6 ) ),
    inference(superposition,[],[f170,f137])).

fof(f170,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k3_xboole_0(X3,X2))
      | k1_xboole_0 != k3_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f133,f62])).

fof(f379,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl5_18
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f382,plain,
    ( spl5_4
    | ~ spl5_18
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f381,f130,f117,f378,f120])).

fof(f381,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f370,f245])).

fof(f245,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f370,plain,
    ( sK2 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ r1_tarski(sK1,sK2)
    | ~ spl5_6 ),
    inference(superposition,[],[f131,f99])).

fof(f207,plain,
    ( spl5_8
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f203,f130,f205])).

fof(f203,plain,
    ( r1_tarski(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_6 ),
    inference(superposition,[],[f96,f131])).

fof(f144,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f140,f142])).

fof(f140,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f138])).

fof(f138,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f67,f137])).

fof(f132,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f93,f130])).

fof(f93,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f47,f88,f86])).

fof(f47,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f35])).

fof(f35,plain,
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

fof(f29,plain,(
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

fof(f128,plain,
    ( ~ spl5_5
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f124,f110,f126])).

fof(f126,plain,
    ( spl5_5
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f124,plain,
    ( sK1 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f123])).

fof(f123,plain,
    ( sK2 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f92])).

fof(f92,plain,
    ( sK2 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f48,f88,f88])).

fof(f48,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f122,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f91,f120,f117])).

fof(f91,plain,
    ( sK2 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f49,f88])).

fof(f49,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f36])).

fof(f115,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f90,f113,f110])).

fof(f90,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f50,f88])).

fof(f50,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (29506)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.49  % (29529)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.49  % (29527)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.49  % (29519)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.49  % (29521)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.50  % (29509)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (29513)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (29524)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (29532)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.25/0.53  % (29510)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.25/0.54  % (29511)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.25/0.54  % (29508)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.25/0.54  % (29507)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.38/0.55  % (29533)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.55  % (29523)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.55  % (29534)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.55  % (29530)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.55  % (29522)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.55  % (29525)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.55  % (29531)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.55  % (29526)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.56  % (29514)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.38/0.56  % (29515)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.38/0.56  % (29518)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.38/0.56  % (29505)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.38/0.57  % (29517)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.59  % (29515)Refutation not found, incomplete strategy% (29515)------------------------------
% 1.38/0.59  % (29515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.59  % (29515)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.59  
% 1.38/0.59  % (29515)Memory used [KB]: 10746
% 1.38/0.59  % (29515)Time elapsed: 0.157 s
% 1.38/0.59  % (29515)------------------------------
% 1.38/0.59  % (29515)------------------------------
% 1.38/0.59  % (29516)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.38/0.60  % (29528)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.60  % (29512)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.60  % (29520)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.61  % (29520)Refutation not found, incomplete strategy% (29520)------------------------------
% 1.38/0.61  % (29520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.61  % (29520)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.61  
% 1.38/0.61  % (29520)Memory used [KB]: 6140
% 1.38/0.61  % (29520)Time elapsed: 0.003 s
% 1.38/0.61  % (29520)------------------------------
% 1.38/0.61  % (29520)------------------------------
% 2.45/0.70  % (29524)Refutation found. Thanks to Tanya!
% 2.45/0.70  % SZS status Theorem for theBenchmark
% 2.45/0.70  % SZS output start Proof for theBenchmark
% 2.45/0.70  fof(f2844,plain,(
% 2.45/0.70    $false),
% 2.45/0.70    inference(avatar_sat_refutation,[],[f115,f122,f128,f132,f144,f207,f382,f386,f392,f1018,f1164,f1319,f1380,f1581,f2837,f2841])).
% 2.45/0.70  fof(f2841,plain,(
% 2.45/0.70    sK1 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK2 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 = sK2),
% 2.45/0.70    introduced(theory_tautology_sat_conflict,[])).
% 2.45/0.70  fof(f2837,plain,(
% 2.45/0.70    spl5_2 | ~spl5_46 | ~spl5_49),
% 2.45/0.70    inference(avatar_split_clause,[],[f2835,f1573,f1378,f113])).
% 2.45/0.70  fof(f113,plain,(
% 2.45/0.70    spl5_2 <=> k1_xboole_0 = sK2),
% 2.45/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.45/0.70  fof(f1378,plain,(
% 2.45/0.70    spl5_46 <=> k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 2.45/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 2.45/0.70  fof(f1573,plain,(
% 2.45/0.70    spl5_49 <=> sK1 = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1))),
% 2.45/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 2.45/0.70  fof(f2835,plain,(
% 2.45/0.70    k1_xboole_0 = sK2 | (~spl5_46 | ~spl5_49)),
% 2.45/0.70    inference(forward_demodulation,[],[f2816,f1379])).
% 2.45/0.70  fof(f1379,plain,(
% 2.45/0.70    k1_xboole_0 = k3_xboole_0(sK2,sK1) | ~spl5_46),
% 2.45/0.70    inference(avatar_component_clause,[],[f1378])).
% 2.45/0.70  fof(f2816,plain,(
% 2.45/0.70    sK2 = k3_xboole_0(sK2,sK1) | ~spl5_49),
% 2.45/0.70    inference(superposition,[],[f202,f1574])).
% 2.45/0.70  fof(f1574,plain,(
% 2.45/0.70    sK1 = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)) | ~spl5_49),
% 2.45/0.70    inference(avatar_component_clause,[],[f1573])).
% 2.45/0.70  fof(f202,plain,(
% 2.45/0.70    ( ! [X4,X3] : (k3_xboole_0(X3,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X4))) = X3) )),
% 2.45/0.70    inference(resolution,[],[f96,f65])).
% 2.45/0.70  fof(f65,plain,(
% 2.45/0.70    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.45/0.70    inference(cnf_transformation,[],[f33])).
% 2.45/0.70  fof(f33,plain,(
% 2.45/0.70    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.45/0.70    inference(ennf_transformation,[],[f10])).
% 2.45/0.70  fof(f10,axiom,(
% 2.45/0.70    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.45/0.70  fof(f96,plain,(
% 2.45/0.70    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.45/0.70    inference(definition_unfolding,[],[f54,f86])).
% 2.45/0.70  fof(f86,plain,(
% 2.45/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 2.45/0.70    inference(definition_unfolding,[],[f57,f85])).
% 2.45/0.70  fof(f85,plain,(
% 2.45/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 2.45/0.70    inference(definition_unfolding,[],[f58,f84])).
% 2.45/0.70  fof(f84,plain,(
% 2.45/0.70    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 2.45/0.70    inference(definition_unfolding,[],[f77,f83])).
% 2.45/0.70  fof(f83,plain,(
% 2.45/0.70    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 2.45/0.70    inference(definition_unfolding,[],[f79,f82])).
% 2.45/0.70  fof(f82,plain,(
% 2.45/0.70    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 2.45/0.70    inference(definition_unfolding,[],[f80,f81])).
% 2.45/0.70  fof(f81,plain,(
% 2.45/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.45/0.70    inference(cnf_transformation,[],[f21])).
% 2.45/0.70  fof(f21,axiom,(
% 2.45/0.70    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.45/0.70  fof(f80,plain,(
% 2.45/0.70    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.45/0.70    inference(cnf_transformation,[],[f20])).
% 2.45/0.70  fof(f20,axiom,(
% 2.45/0.70    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.45/0.70  fof(f79,plain,(
% 2.45/0.70    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.45/0.70    inference(cnf_transformation,[],[f19])).
% 2.45/0.70  fof(f19,axiom,(
% 2.45/0.70    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.45/0.70  fof(f77,plain,(
% 2.45/0.70    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.45/0.70    inference(cnf_transformation,[],[f18])).
% 2.45/0.70  fof(f18,axiom,(
% 2.45/0.70    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.45/0.70  fof(f58,plain,(
% 2.45/0.70    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.45/0.70    inference(cnf_transformation,[],[f17])).
% 2.45/0.70  fof(f17,axiom,(
% 2.45/0.70    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.45/0.70  fof(f57,plain,(
% 2.45/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.45/0.70    inference(cnf_transformation,[],[f25])).
% 2.45/0.70  fof(f25,axiom,(
% 2.45/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.45/0.70  fof(f54,plain,(
% 2.45/0.70    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.45/0.70    inference(cnf_transformation,[],[f13])).
% 2.45/0.70  fof(f13,axiom,(
% 2.45/0.70    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.45/0.70  fof(f1581,plain,(
% 2.45/0.70    spl5_49 | ~spl5_1 | ~spl5_6 | ~spl5_7 | ~spl5_43 | ~spl5_46),
% 2.45/0.70    inference(avatar_split_clause,[],[f1580,f1378,f1317,f142,f130,f110,f1573])).
% 2.45/0.70  fof(f110,plain,(
% 2.45/0.70    spl5_1 <=> sK1 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.45/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.45/0.70  fof(f130,plain,(
% 2.45/0.70    spl5_6 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.45/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.45/0.70  fof(f142,plain,(
% 2.45/0.70    spl5_7 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.45/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.45/0.70  fof(f1317,plain,(
% 2.45/0.70    spl5_43 <=> k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 2.45/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 2.45/0.70  fof(f1580,plain,(
% 2.45/0.70    sK1 = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)) | (~spl5_1 | ~spl5_6 | ~spl5_7 | ~spl5_43 | ~spl5_46)),
% 2.45/0.70    inference(forward_demodulation,[],[f1579,f1017])).
% 2.45/0.70  fof(f1017,plain,(
% 2.45/0.70    sK1 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl5_1),
% 2.45/0.70    inference(avatar_component_clause,[],[f110])).
% 2.45/0.70  fof(f1579,plain,(
% 2.45/0.70    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)) | (~spl5_6 | ~spl5_7 | ~spl5_43 | ~spl5_46)),
% 2.45/0.70    inference(forward_demodulation,[],[f1578,f131])).
% 2.45/0.70  fof(f131,plain,(
% 2.45/0.70    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl5_6),
% 2.45/0.70    inference(avatar_component_clause,[],[f130])).
% 2.45/0.70  fof(f1578,plain,(
% 2.45/0.70    k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)) | (~spl5_7 | ~spl5_43 | ~spl5_46)),
% 2.45/0.70    inference(forward_demodulation,[],[f1577,f906])).
% 2.45/0.70  fof(f906,plain,(
% 2.45/0.70    ( ! [X5] : (k4_xboole_0(X5,k1_xboole_0) = X5) ) | ~spl5_7),
% 2.45/0.70    inference(forward_demodulation,[],[f894,f95])).
% 2.45/0.70  fof(f95,plain,(
% 2.45/0.70    ( ! [X0] : (k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)),k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 2.45/0.70    inference(definition_unfolding,[],[f52,f87])).
% 2.45/0.70  fof(f87,plain,(
% 2.45/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1))) )),
% 2.45/0.70    inference(definition_unfolding,[],[f60,f86])).
% 2.45/0.70  fof(f60,plain,(
% 2.45/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.45/0.70    inference(cnf_transformation,[],[f7])).
% 2.45/0.70  fof(f7,axiom,(
% 2.45/0.70    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).
% 2.45/0.70  fof(f52,plain,(
% 2.45/0.70    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.45/0.70    inference(cnf_transformation,[],[f12])).
% 2.45/0.70  fof(f12,axiom,(
% 2.45/0.70    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.45/0.70  fof(f894,plain,(
% 2.45/0.70    ( ! [X5] : (k4_xboole_0(X5,k1_xboole_0) = k4_xboole_0(k3_tarski(k5_enumset1(X5,X5,X5,X5,X5,X5,k1_xboole_0)),k3_xboole_0(X5,k1_xboole_0))) ) | ~spl5_7),
% 2.45/0.70    inference(superposition,[],[f89,f151])).
% 2.45/0.70  fof(f151,plain,(
% 2.45/0.70    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) ) | ~spl5_7),
% 2.45/0.70    inference(superposition,[],[f150,f55])).
% 2.45/0.70  fof(f55,plain,(
% 2.45/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.45/0.70    inference(cnf_transformation,[],[f1])).
% 2.45/0.70  fof(f1,axiom,(
% 2.45/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.45/0.70  fof(f150,plain,(
% 2.45/0.70    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) ) | ~spl5_7),
% 2.45/0.70    inference(resolution,[],[f148,f65])).
% 2.45/0.70  fof(f148,plain,(
% 2.45/0.70    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl5_7),
% 2.45/0.70    inference(resolution,[],[f147,f69])).
% 2.45/0.70  fof(f69,plain,(
% 2.45/0.70    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.45/0.70    inference(cnf_transformation,[],[f43])).
% 2.45/0.70  fof(f43,plain,(
% 2.45/0.70    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.45/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).
% 2.45/0.70  fof(f42,plain,(
% 2.45/0.70    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.45/0.70    introduced(choice_axiom,[])).
% 2.45/0.70  fof(f41,plain,(
% 2.45/0.70    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.45/0.70    inference(rectify,[],[f40])).
% 2.45/0.70  fof(f40,plain,(
% 2.45/0.70    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.45/0.70    inference(nnf_transformation,[],[f34])).
% 2.45/0.70  fof(f34,plain,(
% 2.45/0.70    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.45/0.70    inference(ennf_transformation,[],[f4])).
% 2.45/0.70  fof(f4,axiom,(
% 2.45/0.70    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.45/0.70  fof(f147,plain,(
% 2.45/0.70    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl5_7),
% 2.45/0.70    inference(forward_demodulation,[],[f146,f137])).
% 2.45/0.70  fof(f137,plain,(
% 2.45/0.70    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.45/0.70    inference(resolution,[],[f136,f65])).
% 2.45/0.70  fof(f136,plain,(
% 2.45/0.70    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.45/0.70    inference(duplicate_literal_removal,[],[f135])).
% 2.45/0.70  fof(f135,plain,(
% 2.45/0.70    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 2.45/0.70    inference(resolution,[],[f70,f69])).
% 2.45/0.70  fof(f70,plain,(
% 2.45/0.70    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.45/0.70    inference(cnf_transformation,[],[f43])).
% 2.45/0.70  fof(f146,plain,(
% 2.45/0.70    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(k1_xboole_0,k1_xboole_0))) ) | ~spl5_7),
% 2.45/0.70    inference(resolution,[],[f143,f62])).
% 2.45/0.70  fof(f62,plain,(
% 2.45/0.70    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.45/0.70    inference(cnf_transformation,[],[f38])).
% 2.45/0.70  fof(f38,plain,(
% 2.45/0.70    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.45/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f37])).
% 2.45/0.70  fof(f37,plain,(
% 2.45/0.70    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 2.45/0.70    introduced(choice_axiom,[])).
% 2.45/0.70  fof(f30,plain,(
% 2.45/0.70    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.45/0.70    inference(ennf_transformation,[],[f28])).
% 2.45/0.70  fof(f28,plain,(
% 2.45/0.70    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.45/0.70    inference(rectify,[],[f6])).
% 2.45/0.70  fof(f6,axiom,(
% 2.45/0.70    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.45/0.70  fof(f143,plain,(
% 2.45/0.70    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_7),
% 2.45/0.70    inference(avatar_component_clause,[],[f142])).
% 2.45/0.70  fof(f89,plain,(
% 2.45/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))),k3_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.45/0.70    inference(definition_unfolding,[],[f59,f87])).
% 2.45/0.70  fof(f59,plain,(
% 2.45/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.45/0.70    inference(cnf_transformation,[],[f8])).
% 2.45/0.70  fof(f8,axiom,(
% 2.45/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.45/0.70  fof(f1577,plain,(
% 2.45/0.70    k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)) = k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k1_xboole_0) | (~spl5_7 | ~spl5_43 | ~spl5_46)),
% 2.45/0.70    inference(forward_demodulation,[],[f1576,f1318])).
% 2.45/0.70  fof(f1318,plain,(
% 2.45/0.70    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl5_43),
% 2.45/0.70    inference(avatar_component_clause,[],[f1317])).
% 2.45/0.70  fof(f1576,plain,(
% 2.45/0.70    k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(sK1,sK2)) = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)) | (~spl5_7 | ~spl5_46)),
% 2.45/0.70    inference(forward_demodulation,[],[f1527,f906])).
% 2.45/0.70  fof(f1527,plain,(
% 2.45/0.70    k4_xboole_0(k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(sK1,sK2)) = k4_xboole_0(k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)),k1_xboole_0) | ~spl5_46),
% 2.45/0.70    inference(superposition,[],[f97,f1379])).
% 2.45/0.70  fof(f97,plain,(
% 2.45/0.70    ( ! [X0,X1] : (k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)) = k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)),k3_xboole_0(X1,X0))) )),
% 2.45/0.70    inference(definition_unfolding,[],[f56,f87,f87])).
% 2.45/0.70  fof(f56,plain,(
% 2.45/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.45/0.70    inference(cnf_transformation,[],[f2])).
% 2.45/0.70  fof(f2,axiom,(
% 2.45/0.70    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.45/0.70  fof(f1380,plain,(
% 2.45/0.70    spl5_46 | ~spl5_43),
% 2.45/0.70    inference(avatar_split_clause,[],[f1349,f1317,f1378])).
% 2.45/0.70  fof(f1349,plain,(
% 2.45/0.70    k1_xboole_0 = k3_xboole_0(sK2,sK1) | ~spl5_43),
% 2.45/0.70    inference(trivial_inequality_removal,[],[f1339])).
% 2.45/0.70  fof(f1339,plain,(
% 2.45/0.70    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(sK2,sK1) | ~spl5_43),
% 2.45/0.70    inference(superposition,[],[f169,f1318])).
% 2.45/0.70  fof(f169,plain,(
% 2.45/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | k3_xboole_0(X1,X0) = k1_xboole_0) )),
% 2.45/0.70    inference(resolution,[],[f133,f66])).
% 2.45/0.70  fof(f66,plain,(
% 2.45/0.70    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.45/0.70    inference(cnf_transformation,[],[f39])).
% 2.45/0.70  fof(f39,plain,(
% 2.45/0.70    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.45/0.70    inference(nnf_transformation,[],[f5])).
% 2.45/0.70  fof(f5,axiom,(
% 2.45/0.70    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.45/0.70  fof(f133,plain,(
% 2.45/0.70    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X1,X0) != k1_xboole_0) )),
% 2.45/0.70    inference(superposition,[],[f67,f55])).
% 2.45/0.70  fof(f67,plain,(
% 2.45/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 2.45/0.70    inference(cnf_transformation,[],[f39])).
% 2.45/0.70  fof(f1319,plain,(
% 2.45/0.70    spl5_43 | ~spl5_1 | spl5_42),
% 2.45/0.70    inference(avatar_split_clause,[],[f1311,f1162,f110,f1317])).
% 2.45/0.70  fof(f1162,plain,(
% 2.45/0.70    spl5_42 <=> r2_hidden(sK0,sK2)),
% 2.45/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 2.45/0.70  fof(f1311,plain,(
% 2.45/0.70    k1_xboole_0 = k3_xboole_0(sK1,sK2) | (~spl5_1 | spl5_42)),
% 2.45/0.70    inference(resolution,[],[f1149,f1163])).
% 2.45/0.70  fof(f1163,plain,(
% 2.45/0.70    ~r2_hidden(sK0,sK2) | spl5_42),
% 2.45/0.70    inference(avatar_component_clause,[],[f1162])).
% 2.45/0.70  fof(f1149,plain,(
% 2.45/0.70    ( ! [X0] : (r2_hidden(sK0,X0) | k1_xboole_0 = k3_xboole_0(sK1,X0)) ) | ~spl5_1),
% 2.45/0.70    inference(resolution,[],[f1082,f66])).
% 2.45/0.70  fof(f1082,plain,(
% 2.45/0.70    ( ! [X69] : (r1_xboole_0(sK1,X69) | r2_hidden(sK0,X69)) ) | ~spl5_1),
% 2.45/0.70    inference(superposition,[],[f98,f1017])).
% 2.45/0.70  fof(f98,plain,(
% 2.45/0.70    ( ! [X0,X1] : (r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.45/0.70    inference(definition_unfolding,[],[f63,f88])).
% 2.45/0.70  fof(f88,plain,(
% 2.45/0.70    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 2.45/0.70    inference(definition_unfolding,[],[f53,f85])).
% 2.45/0.70  fof(f53,plain,(
% 2.45/0.70    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.45/0.70    inference(cnf_transformation,[],[f16])).
% 2.45/0.70  fof(f16,axiom,(
% 2.45/0.70    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.45/0.70  fof(f63,plain,(
% 2.45/0.70    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.45/0.70    inference(cnf_transformation,[],[f31])).
% 2.45/0.70  fof(f31,plain,(
% 2.45/0.70    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.45/0.70    inference(ennf_transformation,[],[f23])).
% 2.45/0.70  fof(f23,axiom,(
% 2.45/0.70    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.45/0.70  fof(f1164,plain,(
% 2.45/0.70    ~spl5_42 | ~spl5_1 | spl5_19),
% 2.45/0.70    inference(avatar_split_clause,[],[f1156,f389,f110,f1162])).
% 2.45/0.70  fof(f389,plain,(
% 2.45/0.70    spl5_19 <=> r1_tarski(sK1,sK2)),
% 2.45/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 2.45/0.70  fof(f1156,plain,(
% 2.45/0.70    ~r2_hidden(sK0,sK2) | (~spl5_1 | spl5_19)),
% 2.45/0.70    inference(resolution,[],[f1084,f390])).
% 2.45/0.70  fof(f390,plain,(
% 2.45/0.70    ~r1_tarski(sK1,sK2) | spl5_19),
% 2.45/0.70    inference(avatar_component_clause,[],[f389])).
% 2.45/0.70  fof(f1084,plain,(
% 2.45/0.70    ( ! [X71] : (r1_tarski(sK1,X71) | ~r2_hidden(sK0,X71)) ) | ~spl5_1),
% 2.45/0.70    inference(superposition,[],[f103,f1017])).
% 2.45/0.70  fof(f103,plain,(
% 2.45/0.70    ( ! [X0,X1] : (r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.45/0.70    inference(definition_unfolding,[],[f75,f88])).
% 2.45/0.70  fof(f75,plain,(
% 2.45/0.70    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.45/0.70    inference(cnf_transformation,[],[f46])).
% 2.45/0.70  fof(f46,plain,(
% 2.45/0.70    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.45/0.70    inference(nnf_transformation,[],[f22])).
% 2.45/0.70  fof(f22,axiom,(
% 2.45/0.70    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.45/0.70  fof(f1018,plain,(
% 2.45/0.70    spl5_1 | spl5_3 | ~spl5_8),
% 2.45/0.70    inference(avatar_split_clause,[],[f1009,f205,f117,f110])).
% 2.45/0.70  fof(f117,plain,(
% 2.45/0.70    spl5_3 <=> k1_xboole_0 = sK1),
% 2.45/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.45/0.70  fof(f205,plain,(
% 2.45/0.70    spl5_8 <=> r1_tarski(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.45/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 2.45/0.70  fof(f1009,plain,(
% 2.45/0.70    k1_xboole_0 = sK1 | sK1 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl5_8),
% 2.45/0.70    inference(resolution,[],[f102,f206])).
% 2.45/0.70  fof(f206,plain,(
% 2.45/0.70    r1_tarski(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl5_8),
% 2.45/0.70    inference(avatar_component_clause,[],[f205])).
% 2.45/0.70  fof(f102,plain,(
% 2.45/0.70    ( ! [X0,X1] : (~r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 2.45/0.70    inference(definition_unfolding,[],[f71,f88,f88])).
% 2.45/0.70  fof(f71,plain,(
% 2.45/0.70    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.45/0.70    inference(cnf_transformation,[],[f45])).
% 2.45/0.70  fof(f45,plain,(
% 2.45/0.70    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.45/0.70    inference(flattening,[],[f44])).
% 2.45/0.70  fof(f44,plain,(
% 2.45/0.70    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.45/0.70    inference(nnf_transformation,[],[f24])).
% 2.45/0.70  fof(f24,axiom,(
% 2.45/0.70    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.45/0.70  fof(f392,plain,(
% 2.45/0.70    ~spl5_19 | spl5_4 | ~spl5_6),
% 2.45/0.70    inference(avatar_split_clause,[],[f369,f130,f120,f389])).
% 2.45/0.70  fof(f120,plain,(
% 2.45/0.70    spl5_4 <=> sK2 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.45/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.45/0.70  fof(f369,plain,(
% 2.45/0.70    sK2 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~r1_tarski(sK1,sK2) | ~spl5_6),
% 2.45/0.70    inference(superposition,[],[f99,f131])).
% 2.45/0.70  fof(f99,plain,(
% 2.45/0.70    ( ! [X0,X1] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.45/0.70    inference(definition_unfolding,[],[f64,f86])).
% 2.45/0.70  fof(f64,plain,(
% 2.45/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.45/0.70    inference(cnf_transformation,[],[f32])).
% 2.45/0.70  fof(f32,plain,(
% 2.45/0.70    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.45/0.70    inference(ennf_transformation,[],[f9])).
% 2.45/0.70  fof(f9,axiom,(
% 2.45/0.70    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.45/0.70  fof(f386,plain,(
% 2.45/0.70    spl5_18),
% 2.45/0.70    inference(avatar_contradiction_clause,[],[f385])).
% 2.45/0.70  fof(f385,plain,(
% 2.45/0.70    $false | spl5_18),
% 2.45/0.70    inference(trivial_inequality_removal,[],[f384])).
% 2.45/0.70  fof(f384,plain,(
% 2.45/0.70    k1_xboole_0 != k1_xboole_0 | spl5_18),
% 2.45/0.70    inference(resolution,[],[f379,f190])).
% 2.45/0.70  fof(f190,plain,(
% 2.45/0.70    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != X0) )),
% 2.45/0.70    inference(resolution,[],[f185,f69])).
% 2.45/0.70  fof(f185,plain,(
% 2.45/0.70    ( ! [X6,X7] : (~r2_hidden(X7,X6) | k1_xboole_0 != X6) )),
% 2.45/0.70    inference(superposition,[],[f170,f137])).
% 2.45/0.70  fof(f170,plain,(
% 2.45/0.70    ( ! [X4,X2,X3] : (~r2_hidden(X4,k3_xboole_0(X3,X2)) | k1_xboole_0 != k3_xboole_0(X2,X3)) )),
% 2.45/0.70    inference(resolution,[],[f133,f62])).
% 2.45/0.70  fof(f379,plain,(
% 2.45/0.70    ~r1_tarski(k1_xboole_0,sK2) | spl5_18),
% 2.45/0.70    inference(avatar_component_clause,[],[f378])).
% 2.45/0.70  fof(f378,plain,(
% 2.45/0.70    spl5_18 <=> r1_tarski(k1_xboole_0,sK2)),
% 2.45/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 2.45/0.70  fof(f382,plain,(
% 2.45/0.70    spl5_4 | ~spl5_18 | ~spl5_3 | ~spl5_6),
% 2.45/0.70    inference(avatar_split_clause,[],[f381,f130,f117,f378,f120])).
% 2.45/0.70  fof(f381,plain,(
% 2.45/0.70    ~r1_tarski(k1_xboole_0,sK2) | sK2 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | (~spl5_3 | ~spl5_6)),
% 2.45/0.70    inference(forward_demodulation,[],[f370,f245])).
% 2.45/0.70  fof(f245,plain,(
% 2.45/0.70    k1_xboole_0 = sK1 | ~spl5_3),
% 2.45/0.70    inference(avatar_component_clause,[],[f117])).
% 2.45/0.70  fof(f370,plain,(
% 2.45/0.70    sK2 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~r1_tarski(sK1,sK2) | ~spl5_6),
% 2.45/0.70    inference(superposition,[],[f131,f99])).
% 2.45/0.70  fof(f207,plain,(
% 2.45/0.70    spl5_8 | ~spl5_6),
% 2.45/0.70    inference(avatar_split_clause,[],[f203,f130,f205])).
% 2.45/0.70  fof(f203,plain,(
% 2.45/0.70    r1_tarski(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl5_6),
% 2.45/0.70    inference(superposition,[],[f96,f131])).
% 2.45/0.70  fof(f144,plain,(
% 2.45/0.70    spl5_7),
% 2.45/0.70    inference(avatar_split_clause,[],[f140,f142])).
% 2.45/0.70  fof(f140,plain,(
% 2.45/0.70    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.45/0.70    inference(equality_resolution,[],[f138])).
% 2.45/0.70  fof(f138,plain,(
% 2.45/0.70    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 2.45/0.70    inference(superposition,[],[f67,f137])).
% 2.45/0.70  fof(f132,plain,(
% 2.45/0.70    spl5_6),
% 2.45/0.70    inference(avatar_split_clause,[],[f93,f130])).
% 2.45/0.70  fof(f93,plain,(
% 2.45/0.70    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.45/0.70    inference(definition_unfolding,[],[f47,f88,f86])).
% 2.45/0.70  fof(f47,plain,(
% 2.45/0.70    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.45/0.70    inference(cnf_transformation,[],[f36])).
% 2.45/0.70  fof(f36,plain,(
% 2.45/0.70    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.45/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f35])).
% 2.45/0.70  fof(f35,plain,(
% 2.45/0.70    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 2.45/0.70    introduced(choice_axiom,[])).
% 2.45/0.70  fof(f29,plain,(
% 2.45/0.70    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.45/0.70    inference(ennf_transformation,[],[f27])).
% 2.45/0.70  fof(f27,negated_conjecture,(
% 2.45/0.70    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.45/0.70    inference(negated_conjecture,[],[f26])).
% 2.45/0.70  fof(f26,conjecture,(
% 2.45/0.70    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.45/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.45/0.70  fof(f128,plain,(
% 2.45/0.70    ~spl5_5 | ~spl5_1),
% 2.45/0.70    inference(avatar_split_clause,[],[f124,f110,f126])).
% 2.45/0.70  fof(f126,plain,(
% 2.45/0.70    spl5_5 <=> sK1 = sK2),
% 2.45/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.45/0.70  fof(f124,plain,(
% 2.45/0.70    sK1 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != sK2),
% 2.45/0.70    inference(inner_rewriting,[],[f123])).
% 2.45/0.70  fof(f123,plain,(
% 2.45/0.70    sK2 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != sK2),
% 2.45/0.70    inference(inner_rewriting,[],[f92])).
% 2.45/0.70  fof(f92,plain,(
% 2.45/0.70    sK2 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.45/0.70    inference(definition_unfolding,[],[f48,f88,f88])).
% 2.45/0.70  fof(f48,plain,(
% 2.45/0.70    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 2.45/0.70    inference(cnf_transformation,[],[f36])).
% 2.45/0.70  fof(f122,plain,(
% 2.45/0.70    ~spl5_3 | ~spl5_4),
% 2.45/0.70    inference(avatar_split_clause,[],[f91,f120,f117])).
% 2.45/0.70  fof(f91,plain,(
% 2.45/0.70    sK2 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 2.45/0.70    inference(definition_unfolding,[],[f49,f88])).
% 2.45/0.70  fof(f49,plain,(
% 2.45/0.70    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 2.45/0.70    inference(cnf_transformation,[],[f36])).
% 2.45/0.70  fof(f115,plain,(
% 2.45/0.70    ~spl5_1 | ~spl5_2),
% 2.45/0.70    inference(avatar_split_clause,[],[f90,f113,f110])).
% 2.45/0.70  fof(f90,plain,(
% 2.45/0.70    k1_xboole_0 != sK2 | sK1 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.45/0.70    inference(definition_unfolding,[],[f50,f88])).
% 2.45/0.70  fof(f50,plain,(
% 2.45/0.70    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 2.45/0.70    inference(cnf_transformation,[],[f36])).
% 2.45/0.70  % SZS output end Proof for theBenchmark
% 2.45/0.70  % (29524)------------------------------
% 2.45/0.70  % (29524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.45/0.70  % (29524)Termination reason: Refutation
% 2.45/0.70  
% 2.45/0.70  % (29524)Memory used [KB]: 13304
% 2.45/0.70  % (29524)Time elapsed: 0.287 s
% 2.45/0.70  % (29524)------------------------------
% 2.45/0.70  % (29524)------------------------------
% 2.45/0.72  % (29500)Success in time 0.358 s
%------------------------------------------------------------------------------
