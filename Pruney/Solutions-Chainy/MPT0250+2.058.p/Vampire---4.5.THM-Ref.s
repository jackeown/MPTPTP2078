%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:27 EST 2020

% Result     : Theorem 2.25s
% Output     : Refutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 310 expanded)
%              Number of leaves         :   25 ( 109 expanded)
%              Depth                    :   18
%              Number of atoms          :  162 ( 393 expanded)
%              Number of equality atoms :   67 ( 274 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1229,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f134,f139,f196,f1185,f1212,f1225,f1228])).

fof(f1228,plain,(
    ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f1227])).

fof(f1227,plain,
    ( $false
    | ~ spl3_4 ),
    inference(resolution,[],[f202,f358])).

fof(f358,plain,(
    ! [X2,X3] : ~ r2_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),X3) ),
    inference(resolution,[],[f354,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f354,plain,(
    ! [X2,X3] : r1_tarski(X3,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) ),
    inference(superposition,[],[f334,f86])).

fof(f86,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f39,f80,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f50,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f334,plain,(
    ! [X14,X12,X10,X15,X13,X11,X9,X16] : r1_tarski(X9,k3_tarski(k6_enumset1(X10,X11,X12,X13,X14,X15,X16,X9))) ),
    inference(resolution,[],[f320,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f320,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : r2_hidden(X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(superposition,[],[f112,f83])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f53,f80,f77,f77])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

fof(f112,plain,(
    ! [X6,X4,X2,X0,X10,X7,X5,X3,X1] : r2_hidden(X10,k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X10)))) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X6,X4,X2,X0,X10,X7,X5,X3,X1,X9] :
      ( r2_hidden(X10,X9)
      | k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X10))) != X9 ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( X8 != X10
      | r2_hidden(X10,X9)
      | k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) != X9 ) ),
    inference(definition_unfolding,[],[f74,f81])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) ),
    inference(definition_unfolding,[],[f54,f80,f76,f77])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] :
      ( X8 != X10
      | r2_hidden(X10,X9)
      | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ( X8 = X10
            | X7 = X10
            | X6 = X10
            | X5 = X10
            | X4 = X10
            | X3 = X10
            | X2 = X10
            | X1 = X10
            | X0 = X10 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X8 != X10
              & X7 != X10
              & X6 != X10
              & X5 != X10
              & X4 != X10
              & X3 != X10
              & X2 != X10
              & X1 != X10
              & X0 != X10 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).

fof(f202,plain,
    ( r2_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl3_4
  <=> r2_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1225,plain,
    ( spl3_4
    | spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f1223,f193,f204,f200])).

fof(f204,plain,
    ( spl3_5
  <=> sK1 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f193,plain,
    ( spl3_3
  <=> r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1223,plain,
    ( sK1 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | r2_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f195,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f195,plain,
    ( r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f193])).

fof(f1212,plain,
    ( spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f1208,f1182,f131])).

fof(f131,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1182,plain,
    ( spl3_10
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f1208,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_10 ),
    inference(resolution,[],[f1184,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f47,f79])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f1184,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f1182])).

fof(f1185,plain,
    ( spl3_10
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f1155,f204,f1182])).

fof(f1155,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl3_5 ),
    inference(superposition,[],[f152,f206])).

fof(f206,plain,
    ( sK1 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f204])).

fof(f152,plain,(
    ! [X2,X3] : r1_tarski(X2,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) ),
    inference(superposition,[],[f85,f86])).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f34,f80])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f196,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f191,f136,f193])).

fof(f136,plain,
    ( spl3_2
  <=> r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f191,plain,
    ( r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f138,f86])).

fof(f138,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f136])).

fof(f139,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f84,f136])).

fof(f84,plain,(
    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) ),
    inference(definition_unfolding,[],[f31,f80,f82])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f79])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f134,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f32,f131])).

fof(f32,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : run_vampire %s %d
% 0.10/0.29  % Computer   : n020.cluster.edu
% 0.10/0.29  % Model      : x86_64 x86_64
% 0.10/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.29  % Memory     : 8042.1875MB
% 0.10/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.29  % CPULimit   : 60
% 0.10/0.29  % WCLimit    : 600
% 0.10/0.29  % DateTime   : Tue Dec  1 15:05:52 EST 2020
% 0.10/0.29  % CPUTime    : 
% 0.15/0.43  % (10670)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.15/0.44  % (10662)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.15/0.44  % (10654)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.15/0.46  % (10649)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.15/0.46  % (10650)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.15/0.46  % (10648)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.15/0.46  % (10648)Refutation not found, incomplete strategy% (10648)------------------------------
% 0.15/0.46  % (10648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.46  % (10648)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.46  
% 0.15/0.46  % (10648)Memory used [KB]: 1663
% 0.15/0.46  % (10648)Time elapsed: 0.106 s
% 0.15/0.46  % (10648)------------------------------
% 0.15/0.46  % (10648)------------------------------
% 0.15/0.47  % (10661)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.15/0.47  % (10660)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.15/0.47  % (10658)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.15/0.47  % (10663)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.15/0.48  % (10677)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.15/0.48  % (10672)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.15/0.48  % (10664)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.15/0.48  % (10657)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.15/0.48  % (10657)Refutation not found, incomplete strategy% (10657)------------------------------
% 0.15/0.48  % (10657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.48  % (10657)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.48  
% 0.15/0.48  % (10657)Memory used [KB]: 10618
% 0.15/0.48  % (10657)Time elapsed: 0.134 s
% 0.15/0.48  % (10657)------------------------------
% 0.15/0.48  % (10657)------------------------------
% 0.15/0.48  % (10658)Refutation not found, incomplete strategy% (10658)------------------------------
% 0.15/0.48  % (10658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.48  % (10668)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.15/0.48  % (10652)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.15/0.48  % (10671)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.15/0.48  % (10674)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.15/0.49  % (10652)Refutation not found, incomplete strategy% (10652)------------------------------
% 0.15/0.49  % (10652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.49  % (10652)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.49  
% 0.15/0.49  % (10652)Memory used [KB]: 6268
% 0.15/0.49  % (10652)Time elapsed: 0.129 s
% 0.15/0.49  % (10652)------------------------------
% 0.15/0.49  % (10652)------------------------------
% 0.15/0.49  % (10658)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.49  
% 0.15/0.49  % (10658)Memory used [KB]: 10618
% 0.15/0.49  % (10658)Time elapsed: 0.132 s
% 0.15/0.49  % (10658)------------------------------
% 0.15/0.49  % (10658)------------------------------
% 0.15/0.49  % (10674)Refutation not found, incomplete strategy% (10674)------------------------------
% 0.15/0.49  % (10674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.49  % (10674)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.49  
% 0.15/0.49  % (10674)Memory used [KB]: 10874
% 0.15/0.49  % (10674)Time elapsed: 0.138 s
% 0.15/0.49  % (10674)------------------------------
% 0.15/0.49  % (10674)------------------------------
% 0.15/0.49  % (10653)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.15/0.49  % (10671)Refutation not found, incomplete strategy% (10671)------------------------------
% 0.15/0.49  % (10671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.49  % (10667)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.15/0.49  % (10666)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.15/0.49  % (10671)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.49  
% 0.15/0.49  % (10671)Memory used [KB]: 1791
% 0.15/0.49  % (10671)Time elapsed: 0.142 s
% 0.15/0.49  % (10671)------------------------------
% 0.15/0.49  % (10671)------------------------------
% 0.15/0.49  % (10676)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.15/0.50  % (10656)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.15/0.50  % (10668)Refutation not found, incomplete strategy% (10668)------------------------------
% 0.15/0.50  % (10668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.50  % (10668)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.50  
% 0.15/0.50  % (10668)Memory used [KB]: 10746
% 0.15/0.50  % (10668)Time elapsed: 0.154 s
% 0.15/0.50  % (10668)------------------------------
% 0.15/0.50  % (10668)------------------------------
% 0.15/0.50  % (10655)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.15/0.51  % (10665)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.15/0.51  % (10651)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.15/0.51  % (10673)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.15/0.52  % (10675)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.15/0.53  % (10673)Refutation not found, incomplete strategy% (10673)------------------------------
% 0.15/0.53  % (10673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.53  % (10659)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.15/0.53  % (10665)Refutation not found, incomplete strategy% (10665)------------------------------
% 0.15/0.53  % (10665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.53  % (10665)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.53  
% 0.15/0.53  % (10665)Memory used [KB]: 10618
% 0.15/0.53  % (10665)Time elapsed: 0.156 s
% 0.15/0.53  % (10665)------------------------------
% 0.15/0.53  % (10665)------------------------------
% 0.15/0.53  % (10659)Refutation not found, incomplete strategy% (10659)------------------------------
% 0.15/0.53  % (10659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.53  % (10669)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.15/0.54  % (10673)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.54  
% 0.15/0.54  % (10673)Memory used [KB]: 6396
% 0.15/0.54  % (10673)Time elapsed: 0.154 s
% 0.15/0.54  % (10673)------------------------------
% 0.15/0.54  % (10673)------------------------------
% 0.15/0.55  % (10659)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.55  
% 0.15/0.55  % (10659)Memory used [KB]: 10618
% 0.15/0.55  % (10659)Time elapsed: 0.166 s
% 0.15/0.55  % (10659)------------------------------
% 0.15/0.55  % (10659)------------------------------
% 0.15/0.55  % (10669)Refutation not found, incomplete strategy% (10669)------------------------------
% 0.15/0.55  % (10669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.55  % (10669)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.55  
% 0.15/0.55  % (10669)Memory used [KB]: 1918
% 0.15/0.55  % (10669)Time elapsed: 0.192 s
% 0.15/0.55  % (10669)------------------------------
% 0.15/0.55  % (10669)------------------------------
% 2.11/0.59  % (10678)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.11/0.59  % (10678)Refutation not found, incomplete strategy% (10678)------------------------------
% 2.11/0.59  % (10678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.59  % (10678)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.59  
% 2.11/0.59  % (10678)Memory used [KB]: 6140
% 2.11/0.59  % (10678)Time elapsed: 0.090 s
% 2.11/0.59  % (10678)------------------------------
% 2.11/0.59  % (10678)------------------------------
% 2.25/0.61  % (10679)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.25/0.62  % (10664)Refutation found. Thanks to Tanya!
% 2.25/0.62  % SZS status Theorem for theBenchmark
% 2.25/0.62  % SZS output start Proof for theBenchmark
% 2.25/0.62  fof(f1229,plain,(
% 2.25/0.62    $false),
% 2.25/0.62    inference(avatar_sat_refutation,[],[f134,f139,f196,f1185,f1212,f1225,f1228])).
% 2.25/0.62  fof(f1228,plain,(
% 2.25/0.62    ~spl3_4),
% 2.25/0.62    inference(avatar_contradiction_clause,[],[f1227])).
% 2.25/0.62  fof(f1227,plain,(
% 2.25/0.62    $false | ~spl3_4),
% 2.25/0.62    inference(resolution,[],[f202,f358])).
% 2.25/0.62  fof(f358,plain,(
% 2.25/0.62    ( ! [X2,X3] : (~r2_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),X3)) )),
% 2.25/0.62    inference(resolution,[],[f354,f43])).
% 2.25/0.62  fof(f43,plain,(
% 2.25/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 2.25/0.62    inference(cnf_transformation,[],[f29])).
% 2.25/0.62  fof(f29,plain,(
% 2.25/0.62    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 2.25/0.62    inference(ennf_transformation,[],[f4])).
% 2.25/0.62  fof(f4,axiom,(
% 2.25/0.62    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 2.25/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).
% 2.25/0.62  fof(f354,plain,(
% 2.25/0.62    ( ! [X2,X3] : (r1_tarski(X3,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))) )),
% 2.25/0.62    inference(superposition,[],[f334,f86])).
% 2.25/0.62  fof(f86,plain,(
% 2.25/0.62    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.25/0.62    inference(definition_unfolding,[],[f39,f80,f38])).
% 2.25/0.62  fof(f38,plain,(
% 2.25/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.25/0.62    inference(cnf_transformation,[],[f3])).
% 2.25/0.62  fof(f3,axiom,(
% 2.25/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.25/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.25/0.62  fof(f80,plain,(
% 2.25/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.25/0.62    inference(definition_unfolding,[],[f36,f79])).
% 2.25/0.62  fof(f79,plain,(
% 2.25/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.25/0.62    inference(definition_unfolding,[],[f37,f78])).
% 2.25/0.62  fof(f78,plain,(
% 2.25/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.25/0.62    inference(definition_unfolding,[],[f44,f77])).
% 2.25/0.62  fof(f77,plain,(
% 2.25/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.25/0.62    inference(definition_unfolding,[],[f49,f76])).
% 2.25/0.62  fof(f76,plain,(
% 2.25/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.25/0.62    inference(definition_unfolding,[],[f50,f75])).
% 2.25/0.62  fof(f75,plain,(
% 2.25/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.25/0.62    inference(definition_unfolding,[],[f51,f52])).
% 2.25/0.62  fof(f52,plain,(
% 2.25/0.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.25/0.62    inference(cnf_transformation,[],[f18])).
% 2.25/0.62  fof(f18,axiom,(
% 2.25/0.62    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.25/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.25/0.62  fof(f51,plain,(
% 2.25/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.25/0.62    inference(cnf_transformation,[],[f17])).
% 2.25/0.62  fof(f17,axiom,(
% 2.25/0.62    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.25/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.25/0.62  fof(f50,plain,(
% 2.25/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.25/0.62    inference(cnf_transformation,[],[f16])).
% 2.25/0.62  fof(f16,axiom,(
% 2.25/0.62    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.25/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.25/0.62  fof(f49,plain,(
% 2.25/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.25/0.62    inference(cnf_transformation,[],[f15])).
% 2.25/0.62  fof(f15,axiom,(
% 2.25/0.62    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.25/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.25/0.62  fof(f44,plain,(
% 2.25/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.25/0.62    inference(cnf_transformation,[],[f14])).
% 2.25/0.62  fof(f14,axiom,(
% 2.25/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.25/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.25/0.62  fof(f37,plain,(
% 2.25/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.25/0.62    inference(cnf_transformation,[],[f13])).
% 2.25/0.62  fof(f13,axiom,(
% 2.25/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.25/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.25/0.62  fof(f36,plain,(
% 2.25/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.25/0.62    inference(cnf_transformation,[],[f20])).
% 2.25/0.62  fof(f20,axiom,(
% 2.25/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.25/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.25/0.62  fof(f39,plain,(
% 2.25/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.25/0.62    inference(cnf_transformation,[],[f8])).
% 2.25/0.62  fof(f8,axiom,(
% 2.25/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.25/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.25/0.62  fof(f334,plain,(
% 2.25/0.62    ( ! [X14,X12,X10,X15,X13,X11,X9,X16] : (r1_tarski(X9,k3_tarski(k6_enumset1(X10,X11,X12,X13,X14,X15,X16,X9)))) )),
% 2.25/0.62    inference(resolution,[],[f320,f41])).
% 2.25/0.62  fof(f41,plain,(
% 2.25/0.62    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 2.25/0.62    inference(cnf_transformation,[],[f26])).
% 2.25/0.62  fof(f26,plain,(
% 2.25/0.62    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 2.25/0.62    inference(ennf_transformation,[],[f19])).
% 2.25/0.62  fof(f19,axiom,(
% 2.25/0.62    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 2.25/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 2.25/0.62  fof(f320,plain,(
% 2.25/0.62    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 2.25/0.62    inference(superposition,[],[f112,f83])).
% 2.25/0.62  fof(f83,plain,(
% 2.25/0.62    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7)))) )),
% 2.25/0.62    inference(definition_unfolding,[],[f53,f80,f77,f77])).
% 2.25/0.62  fof(f53,plain,(
% 2.25/0.62    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 2.25/0.62    inference(cnf_transformation,[],[f10])).
% 2.25/0.62  fof(f10,axiom,(
% 2.25/0.62    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 2.25/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).
% 2.25/0.62  fof(f112,plain,(
% 2.25/0.62    ( ! [X6,X4,X2,X0,X10,X7,X5,X3,X1] : (r2_hidden(X10,k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X10))))) )),
% 2.25/0.62    inference(equality_resolution,[],[f111])).
% 2.25/0.62  fof(f111,plain,(
% 2.25/0.62    ( ! [X6,X4,X2,X0,X10,X7,X5,X3,X1,X9] : (r2_hidden(X10,X9) | k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X10))) != X9) )),
% 2.25/0.62    inference(equality_resolution,[],[f91])).
% 2.25/0.62  fof(f91,plain,(
% 2.25/0.62    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (X8 != X10 | r2_hidden(X10,X9) | k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8))) != X9) )),
% 2.25/0.62    inference(definition_unfolding,[],[f74,f81])).
% 2.25/0.62  fof(f81,plain,(
% 2.25/0.62    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X6,X7,X8)))) )),
% 2.25/0.62    inference(definition_unfolding,[],[f54,f80,f76,f77])).
% 2.25/0.62  fof(f54,plain,(
% 2.25/0.62    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 2.25/0.62    inference(cnf_transformation,[],[f11])).
% 2.25/0.62  fof(f11,axiom,(
% 2.25/0.62    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 2.25/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).
% 2.25/0.62  fof(f74,plain,(
% 2.25/0.62    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1,X9] : (X8 != X10 | r2_hidden(X10,X9) | k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X9) )),
% 2.25/0.62    inference(cnf_transformation,[],[f30])).
% 2.25/0.62  fof(f30,plain,(
% 2.25/0.62    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> (X8 = X10 | X7 = X10 | X6 = X10 | X5 = X10 | X4 = X10 | X3 = X10 | X2 = X10 | X1 = X10 | X0 = X10)))),
% 2.25/0.62    inference(ennf_transformation,[],[f9])).
% 2.25/0.62  fof(f9,axiom,(
% 2.25/0.62    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X9 <=> ! [X10] : (r2_hidden(X10,X9) <=> ~(X8 != X10 & X7 != X10 & X6 != X10 & X5 != X10 & X4 != X10 & X3 != X10 & X2 != X10 & X1 != X10 & X0 != X10)))),
% 2.25/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_enumset1)).
% 2.25/0.62  fof(f202,plain,(
% 2.25/0.62    r2_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1) | ~spl3_4),
% 2.25/0.62    inference(avatar_component_clause,[],[f200])).
% 2.25/0.62  fof(f200,plain,(
% 2.25/0.62    spl3_4 <=> r2_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1)),
% 2.25/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.25/0.62  fof(f1225,plain,(
% 2.25/0.62    spl3_4 | spl3_5 | ~spl3_3),
% 2.25/0.62    inference(avatar_split_clause,[],[f1223,f193,f204,f200])).
% 2.25/0.62  fof(f204,plain,(
% 2.25/0.62    spl3_5 <=> sK1 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 2.25/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.25/0.62  fof(f193,plain,(
% 2.25/0.62    spl3_3 <=> r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1)),
% 2.25/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.25/0.62  fof(f1223,plain,(
% 2.25/0.62    sK1 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | r2_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1) | ~spl3_3),
% 2.25/0.62    inference(resolution,[],[f195,f42])).
% 2.25/0.62  fof(f42,plain,(
% 2.25/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 2.25/0.62    inference(cnf_transformation,[],[f28])).
% 2.25/0.62  fof(f28,plain,(
% 2.25/0.62    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 2.25/0.62    inference(flattening,[],[f27])).
% 2.25/0.62  fof(f27,plain,(
% 2.25/0.62    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 2.25/0.62    inference(ennf_transformation,[],[f24])).
% 2.25/0.62  fof(f24,plain,(
% 2.25/0.62    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 2.25/0.62    inference(unused_predicate_definition_removal,[],[f2])).
% 2.25/0.62  fof(f2,axiom,(
% 2.25/0.62    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.25/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 2.25/0.62  fof(f195,plain,(
% 2.25/0.62    r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1) | ~spl3_3),
% 2.25/0.62    inference(avatar_component_clause,[],[f193])).
% 2.25/0.62  fof(f1212,plain,(
% 2.25/0.62    spl3_1 | ~spl3_10),
% 2.25/0.62    inference(avatar_split_clause,[],[f1208,f1182,f131])).
% 2.25/0.62  fof(f131,plain,(
% 2.25/0.62    spl3_1 <=> r2_hidden(sK0,sK1)),
% 2.25/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.25/0.62  fof(f1182,plain,(
% 2.25/0.62    spl3_10 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 2.25/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.25/0.62  fof(f1208,plain,(
% 2.25/0.62    r2_hidden(sK0,sK1) | ~spl3_10),
% 2.25/0.62    inference(resolution,[],[f1184,f89])).
% 2.25/0.62  fof(f89,plain,(
% 2.25/0.62    ( ! [X2,X0,X1] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 2.25/0.62    inference(definition_unfolding,[],[f47,f79])).
% 2.25/0.62  fof(f47,plain,(
% 2.25/0.62    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 2.25/0.62    inference(cnf_transformation,[],[f21])).
% 2.25/0.62  fof(f21,axiom,(
% 2.25/0.62    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.25/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 2.25/0.62  fof(f1184,plain,(
% 2.25/0.62    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | ~spl3_10),
% 2.25/0.62    inference(avatar_component_clause,[],[f1182])).
% 2.25/0.62  fof(f1185,plain,(
% 2.25/0.62    spl3_10 | ~spl3_5),
% 2.25/0.62    inference(avatar_split_clause,[],[f1155,f204,f1182])).
% 2.25/0.62  fof(f1155,plain,(
% 2.25/0.62    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | ~spl3_5),
% 2.25/0.62    inference(superposition,[],[f152,f206])).
% 2.25/0.62  fof(f206,plain,(
% 2.25/0.62    sK1 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~spl3_5),
% 2.25/0.62    inference(avatar_component_clause,[],[f204])).
% 2.25/0.62  fof(f152,plain,(
% 2.25/0.62    ( ! [X2,X3] : (r1_tarski(X2,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))) )),
% 2.25/0.62    inference(superposition,[],[f85,f86])).
% 2.25/0.62  fof(f85,plain,(
% 2.25/0.62    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.25/0.62    inference(definition_unfolding,[],[f34,f80])).
% 2.25/0.62  fof(f34,plain,(
% 2.25/0.62    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.25/0.62    inference(cnf_transformation,[],[f5])).
% 2.25/0.62  fof(f5,axiom,(
% 2.25/0.62    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.25/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.25/0.62  fof(f196,plain,(
% 2.25/0.62    spl3_3 | ~spl3_2),
% 2.25/0.62    inference(avatar_split_clause,[],[f191,f136,f193])).
% 2.25/0.62  fof(f136,plain,(
% 2.25/0.62    spl3_2 <=> r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1)),
% 2.25/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.25/0.62  fof(f191,plain,(
% 2.25/0.62    r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),sK1) | ~spl3_2),
% 2.25/0.62    inference(forward_demodulation,[],[f138,f86])).
% 2.25/0.62  fof(f138,plain,(
% 2.25/0.62    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) | ~spl3_2),
% 2.25/0.62    inference(avatar_component_clause,[],[f136])).
% 2.25/0.62  fof(f139,plain,(
% 2.25/0.62    spl3_2),
% 2.25/0.62    inference(avatar_split_clause,[],[f84,f136])).
% 2.25/0.62  fof(f84,plain,(
% 2.25/0.62    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1)),
% 2.25/0.62    inference(definition_unfolding,[],[f31,f80,f82])).
% 2.25/0.62  fof(f82,plain,(
% 2.25/0.62    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.25/0.62    inference(definition_unfolding,[],[f33,f79])).
% 2.25/0.62  fof(f33,plain,(
% 2.25/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.25/0.62    inference(cnf_transformation,[],[f12])).
% 2.25/0.62  fof(f12,axiom,(
% 2.25/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.25/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.25/0.62  fof(f31,plain,(
% 2.25/0.62    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 2.25/0.62    inference(cnf_transformation,[],[f25])).
% 2.25/0.62  fof(f25,plain,(
% 2.25/0.62    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 2.25/0.62    inference(ennf_transformation,[],[f23])).
% 2.25/0.62  fof(f23,negated_conjecture,(
% 2.25/0.62    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 2.25/0.62    inference(negated_conjecture,[],[f22])).
% 2.25/0.62  fof(f22,conjecture,(
% 2.25/0.62    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 2.25/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 2.25/0.62  fof(f134,plain,(
% 2.25/0.62    ~spl3_1),
% 2.25/0.62    inference(avatar_split_clause,[],[f32,f131])).
% 2.25/0.62  fof(f32,plain,(
% 2.25/0.62    ~r2_hidden(sK0,sK1)),
% 2.25/0.62    inference(cnf_transformation,[],[f25])).
% 2.25/0.62  % SZS output end Proof for theBenchmark
% 2.25/0.62  % (10664)------------------------------
% 2.25/0.62  % (10664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.25/0.62  % (10664)Termination reason: Refutation
% 2.25/0.62  
% 2.25/0.62  % (10664)Memory used [KB]: 12281
% 2.25/0.62  % (10664)Time elapsed: 0.242 s
% 2.25/0.62  % (10664)------------------------------
% 2.25/0.62  % (10664)------------------------------
% 2.25/0.62  % (10647)Success in time 0.306 s
%------------------------------------------------------------------------------
