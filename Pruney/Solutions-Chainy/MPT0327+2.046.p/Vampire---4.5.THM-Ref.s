%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:54 EST 2020

% Result     : Theorem 2.82s
% Output     : Refutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 150 expanded)
%              Number of leaves         :   26 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  281 ( 357 expanded)
%              Number of equality atoms :  106 ( 138 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1639,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f545,f553,f659,f1238,f1318,f1500,f1558,f1637])).

fof(f1637,plain,(
    spl3_28 ),
    inference(avatar_contradiction_clause,[],[f1630])).

fof(f1630,plain,
    ( $false
    | spl3_28 ),
    inference(unit_resulting_resolution,[],[f64,f1572])).

fof(f1572,plain,
    ( ! [X1] : ~ r1_tarski(k1_tarski(sK0),X1)
    | spl3_28 ),
    inference(subsumption_resolution,[],[f1570,f63])).

fof(f63,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f1570,plain,
    ( ! [X1] :
        ( sK1 != k5_xboole_0(sK1,k1_xboole_0)
        | ~ r1_tarski(k1_tarski(sK0),X1) )
    | spl3_28 ),
    inference(superposition,[],[f1557,f281])).

fof(f281,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k5_xboole_0(X2,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f267])).

fof(f267,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k5_xboole_0(X2,X2)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f53,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f48,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f1557,plain,
    ( sK1 != k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))
    | spl3_28 ),
    inference(avatar_component_clause,[],[f1555])).

fof(f1555,plain,
    ( spl3_28
  <=> sK1 = k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f64,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f1558,plain,
    ( ~ spl3_28
    | spl3_27 ),
    inference(avatar_split_clause,[],[f1553,f1480,f1555])).

fof(f1480,plain,
    ( spl3_27
  <=> sK1 = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f1553,plain,
    ( sK1 != k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))
    | spl3_27 ),
    inference(superposition,[],[f1482,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1482,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | spl3_27 ),
    inference(avatar_component_clause,[],[f1480])).

fof(f1500,plain,
    ( ~ spl3_27
    | ~ spl3_16
    | spl3_24 ),
    inference(avatar_split_clause,[],[f1499,f1235,f550,f1480])).

fof(f550,plain,
    ( spl3_16
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f1235,plain,
    ( spl3_24
  <=> sK1 = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f1499,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl3_16
    | spl3_24 ),
    inference(subsumption_resolution,[],[f1495,f551])).

fof(f551,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f550])).

fof(f1495,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl3_24 ),
    inference(superposition,[],[f1237,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f48,f85])).

fof(f85,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f46,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1237,plain,
    ( sK1 != k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f1235])).

fof(f1318,plain,
    ( spl3_14
    | spl3_23 ),
    inference(avatar_contradiction_clause,[],[f1317])).

fof(f1317,plain,
    ( $false
    | spl3_14
    | spl3_23 ),
    inference(subsumption_resolution,[],[f1311,f446])).

fof(f446,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK0)))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f444])).

fof(f444,plain,
    ( spl3_14
  <=> r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f1311,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK0)))
    | spl3_23 ),
    inference(resolution,[],[f1233,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f1233,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f1231])).

fof(f1231,plain,
    ( spl3_23
  <=> r1_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f1238,plain,
    ( ~ spl3_23
    | ~ spl3_24
    | spl3_1 ),
    inference(avatar_split_clause,[],[f1219,f72,f1235,f1231])).

fof(f72,plain,
    ( spl3_1
  <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1219,plain,
    ( sK1 != k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ r1_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))
    | spl3_1 ),
    inference(superposition,[],[f74,f336])).

fof(f336,plain,(
    ! [X2,X3] :
      ( k5_xboole_0(X3,X2) = k2_xboole_0(X3,X2)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f334,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f334,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k5_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f142,f116])).

fof(f116,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2)) ),
    inference(superposition,[],[f48,f49])).

fof(f142,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))) ),
    inference(superposition,[],[f47,f45])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f74,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f659,plain,
    ( ~ spl3_2
    | spl3_16 ),
    inference(avatar_contradiction_clause,[],[f658])).

fof(f658,plain,
    ( $false
    | ~ spl3_2
    | spl3_16 ),
    inference(subsumption_resolution,[],[f656,f79])).

fof(f79,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f656,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_16 ),
    inference(resolution,[],[f552,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f552,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f550])).

fof(f553,plain,
    ( ~ spl3_16
    | spl3_15 ),
    inference(avatar_split_clause,[],[f548,f476,f550])).

fof(f476,plain,
    ( spl3_15
  <=> r2_hidden(sK0,k3_xboole_0(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f548,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl3_15 ),
    inference(subsumption_resolution,[],[f546,f81])).

fof(f81,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f69,f50])).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f69,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f546,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl3_15 ),
    inference(superposition,[],[f477,f85])).

fof(f477,plain,
    ( ~ r2_hidden(sK0,k3_xboole_0(sK1,k1_tarski(sK0)))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f476])).

fof(f545,plain,
    ( ~ spl3_15
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f544,f444,f77,f476])).

fof(f544,plain,
    ( ~ r2_hidden(sK0,k3_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f539,f79])).

fof(f539,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k3_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl3_14 ),
    inference(resolution,[],[f445,f162])).

fof(f162,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k4_xboole_0(X2,X3))
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,k3_xboole_0(X2,X3)) ) ),
    inference(superposition,[],[f59,f48])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f445,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f444])).

fof(f80,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f37,f77])).

fof(f37,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f75,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f38,f72])).

fof(f38,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:15:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.43/0.55  % (8068)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.43/0.56  % (8079)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.43/0.56  % (8071)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.63/0.57  % (8082)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.63/0.58  % (8088)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.63/0.58  % (8069)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.63/0.58  % (8075)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.63/0.58  % (8082)Refutation not found, incomplete strategy% (8082)------------------------------
% 1.63/0.58  % (8082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.59  % (8082)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.59  
% 1.63/0.59  % (8082)Memory used [KB]: 1663
% 1.63/0.59  % (8082)Time elapsed: 0.148 s
% 1.63/0.59  % (8082)------------------------------
% 1.63/0.59  % (8082)------------------------------
% 1.63/0.59  % (8070)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.63/0.59  % (8073)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.63/0.59  % (8072)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.63/0.60  % (8096)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.63/0.60  % (8095)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.63/0.60  % (8069)Refutation not found, incomplete strategy% (8069)------------------------------
% 1.63/0.60  % (8069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.60  % (8069)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.60  
% 1.63/0.60  % (8069)Memory used [KB]: 1663
% 1.63/0.60  % (8069)Time elapsed: 0.163 s
% 1.63/0.60  % (8069)------------------------------
% 1.63/0.60  % (8069)------------------------------
% 1.63/0.60  % (8087)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.63/0.60  % (8086)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.63/0.60  % (8093)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.63/0.61  % (8086)Refutation not found, incomplete strategy% (8086)------------------------------
% 1.63/0.61  % (8086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.61  % (8086)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.61  
% 1.63/0.61  % (8086)Memory used [KB]: 1791
% 1.63/0.61  % (8086)Time elapsed: 0.169 s
% 1.63/0.61  % (8086)------------------------------
% 1.63/0.61  % (8086)------------------------------
% 1.63/0.61  % (8090)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.63/0.62  % (8091)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.63/0.62  % (8098)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.63/0.62  % (8098)Refutation not found, incomplete strategy% (8098)------------------------------
% 1.63/0.62  % (8098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.62  % (8098)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.62  
% 1.63/0.62  % (8098)Memory used [KB]: 1663
% 1.63/0.62  % (8098)Time elapsed: 0.134 s
% 1.63/0.62  % (8098)------------------------------
% 1.63/0.62  % (8098)------------------------------
% 1.63/0.62  % (8092)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.63/0.63  % (8097)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.63/0.63  % (8094)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.63/0.63  % (8083)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.63/0.63  % (8085)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.63/0.63  % (8089)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.63/0.63  % (8081)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.63/0.63  % (8085)Refutation not found, incomplete strategy% (8085)------------------------------
% 1.63/0.63  % (8085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.63  % (8085)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.63  
% 1.63/0.63  % (8085)Memory used [KB]: 10618
% 1.63/0.63  % (8085)Time elapsed: 0.195 s
% 1.63/0.63  % (8085)------------------------------
% 1.63/0.63  % (8085)------------------------------
% 1.63/0.64  % (8078)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.63/0.64  % (8077)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.63/0.64  % (8076)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.63/0.64  % (8080)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.63/0.64  % (8074)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.82/0.77  % (8090)Refutation found. Thanks to Tanya!
% 2.82/0.77  % SZS status Theorem for theBenchmark
% 2.82/0.78  % (8122)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.82/0.79  % SZS output start Proof for theBenchmark
% 2.82/0.79  fof(f1639,plain,(
% 2.82/0.79    $false),
% 2.82/0.79    inference(avatar_sat_refutation,[],[f75,f80,f545,f553,f659,f1238,f1318,f1500,f1558,f1637])).
% 2.82/0.79  fof(f1637,plain,(
% 2.82/0.79    spl3_28),
% 2.82/0.79    inference(avatar_contradiction_clause,[],[f1630])).
% 2.82/0.79  fof(f1630,plain,(
% 2.82/0.79    $false | spl3_28),
% 2.82/0.79    inference(unit_resulting_resolution,[],[f64,f1572])).
% 2.82/0.79  fof(f1572,plain,(
% 2.82/0.79    ( ! [X1] : (~r1_tarski(k1_tarski(sK0),X1)) ) | spl3_28),
% 2.82/0.79    inference(subsumption_resolution,[],[f1570,f63])).
% 2.82/0.79  fof(f63,plain,(
% 2.82/0.79    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.82/0.79    inference(cnf_transformation,[],[f6])).
% 2.82/0.79  fof(f6,axiom,(
% 2.82/0.79    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.82/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.82/0.79  fof(f1570,plain,(
% 2.82/0.79    ( ! [X1] : (sK1 != k5_xboole_0(sK1,k1_xboole_0) | ~r1_tarski(k1_tarski(sK0),X1)) ) | spl3_28),
% 2.82/0.79    inference(superposition,[],[f1557,f281])).
% 2.82/0.79  fof(f281,plain,(
% 2.82/0.79    ( ! [X2,X3] : (k1_xboole_0 = k5_xboole_0(X2,X2) | ~r1_tarski(X2,X3)) )),
% 2.82/0.79    inference(duplicate_literal_removal,[],[f267])).
% 2.82/0.79  fof(f267,plain,(
% 2.82/0.79    ( ! [X2,X3] : (k1_xboole_0 = k5_xboole_0(X2,X2) | ~r1_tarski(X2,X3) | ~r1_tarski(X2,X3)) )),
% 2.82/0.79    inference(superposition,[],[f53,f115])).
% 2.82/0.79  fof(f115,plain,(
% 2.82/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X1)) )),
% 2.82/0.79    inference(superposition,[],[f48,f46])).
% 2.82/0.79  fof(f46,plain,(
% 2.82/0.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.82/0.79    inference(cnf_transformation,[],[f23])).
% 2.82/0.79  fof(f23,plain,(
% 2.82/0.79    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.82/0.79    inference(ennf_transformation,[],[f5])).
% 2.82/0.79  fof(f5,axiom,(
% 2.82/0.79    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.82/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.82/0.79  fof(f48,plain,(
% 2.82/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.82/0.79    inference(cnf_transformation,[],[f4])).
% 2.82/0.79  fof(f4,axiom,(
% 2.82/0.79    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.82/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.82/0.79  fof(f53,plain,(
% 2.82/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.82/0.79    inference(cnf_transformation,[],[f34])).
% 2.82/0.79  fof(f34,plain,(
% 2.82/0.79    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.82/0.79    inference(nnf_transformation,[],[f3])).
% 2.82/0.79  fof(f3,axiom,(
% 2.82/0.79    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.82/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.82/0.79  fof(f1557,plain,(
% 2.82/0.79    sK1 != k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) | spl3_28),
% 2.82/0.79    inference(avatar_component_clause,[],[f1555])).
% 2.82/0.79  fof(f1555,plain,(
% 2.82/0.79    spl3_28 <=> sK1 = k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))),
% 2.82/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 2.82/0.79  fof(f64,plain,(
% 2.82/0.79    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 2.82/0.79    inference(cnf_transformation,[],[f18])).
% 2.82/0.79  fof(f18,axiom,(
% 2.82/0.79    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 2.82/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 2.82/0.79  fof(f1558,plain,(
% 2.82/0.79    ~spl3_28 | spl3_27),
% 2.82/0.79    inference(avatar_split_clause,[],[f1553,f1480,f1555])).
% 2.82/0.79  fof(f1480,plain,(
% 2.82/0.79    spl3_27 <=> sK1 = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.82/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 2.82/0.79  fof(f1553,plain,(
% 2.82/0.79    sK1 != k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) | spl3_27),
% 2.82/0.79    inference(superposition,[],[f1482,f45])).
% 2.82/0.79  fof(f45,plain,(
% 2.82/0.79    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.82/0.79    inference(cnf_transformation,[],[f8])).
% 2.82/0.79  fof(f8,axiom,(
% 2.82/0.79    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.82/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.82/0.79  fof(f1482,plain,(
% 2.82/0.79    sK1 != k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | spl3_27),
% 2.82/0.79    inference(avatar_component_clause,[],[f1480])).
% 2.82/0.79  fof(f1500,plain,(
% 2.82/0.79    ~spl3_27 | ~spl3_16 | spl3_24),
% 2.82/0.79    inference(avatar_split_clause,[],[f1499,f1235,f550,f1480])).
% 2.82/0.79  fof(f550,plain,(
% 2.82/0.79    spl3_16 <=> r1_tarski(k1_tarski(sK0),sK1)),
% 2.82/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 2.82/0.79  fof(f1235,plain,(
% 2.82/0.79    spl3_24 <=> sK1 = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.82/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.82/0.79  fof(f1499,plain,(
% 2.82/0.79    sK1 != k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | (~spl3_16 | spl3_24)),
% 2.82/0.79    inference(subsumption_resolution,[],[f1495,f551])).
% 2.82/0.79  fof(f551,plain,(
% 2.82/0.79    r1_tarski(k1_tarski(sK0),sK1) | ~spl3_16),
% 2.82/0.79    inference(avatar_component_clause,[],[f550])).
% 2.82/0.79  fof(f1495,plain,(
% 2.82/0.79    sK1 != k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | ~r1_tarski(k1_tarski(sK0),sK1) | spl3_24),
% 2.82/0.79    inference(superposition,[],[f1237,f130])).
% 2.82/0.79  fof(f130,plain,(
% 2.82/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,X1) | ~r1_tarski(X1,X0)) )),
% 2.82/0.79    inference(superposition,[],[f48,f85])).
% 2.82/0.79  fof(f85,plain,(
% 2.82/0.79    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 2.82/0.79    inference(superposition,[],[f46,f49])).
% 2.82/0.79  fof(f49,plain,(
% 2.82/0.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.82/0.79    inference(cnf_transformation,[],[f1])).
% 2.82/0.79  fof(f1,axiom,(
% 2.82/0.79    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.82/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.82/0.79  fof(f1237,plain,(
% 2.82/0.79    sK1 != k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | spl3_24),
% 2.82/0.79    inference(avatar_component_clause,[],[f1235])).
% 2.82/0.79  fof(f1318,plain,(
% 2.82/0.79    spl3_14 | spl3_23),
% 2.82/0.79    inference(avatar_contradiction_clause,[],[f1317])).
% 2.82/0.79  fof(f1317,plain,(
% 2.82/0.79    $false | (spl3_14 | spl3_23)),
% 2.82/0.79    inference(subsumption_resolution,[],[f1311,f446])).
% 2.82/0.79  fof(f446,plain,(
% 2.82/0.79    ~r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK0))) | spl3_14),
% 2.82/0.79    inference(avatar_component_clause,[],[f444])).
% 2.82/0.79  fof(f444,plain,(
% 2.82/0.79    spl3_14 <=> r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK0)))),
% 2.82/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.82/0.79  fof(f1311,plain,(
% 2.82/0.79    r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK0))) | spl3_23),
% 2.82/0.79    inference(resolution,[],[f1233,f57])).
% 2.82/0.79  fof(f57,plain,(
% 2.82/0.79    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.82/0.79    inference(cnf_transformation,[],[f25])).
% 2.82/0.79  fof(f25,plain,(
% 2.82/0.79    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.82/0.79    inference(ennf_transformation,[],[f16])).
% 2.82/0.79  fof(f16,axiom,(
% 2.82/0.79    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.82/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.82/0.79  fof(f1233,plain,(
% 2.82/0.79    ~r1_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) | spl3_23),
% 2.82/0.79    inference(avatar_component_clause,[],[f1231])).
% 2.82/0.79  fof(f1231,plain,(
% 2.82/0.79    spl3_23 <=> r1_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))),
% 2.82/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 2.82/0.79  fof(f1238,plain,(
% 2.82/0.79    ~spl3_23 | ~spl3_24 | spl3_1),
% 2.82/0.79    inference(avatar_split_clause,[],[f1219,f72,f1235,f1231])).
% 2.82/0.79  fof(f72,plain,(
% 2.82/0.79    spl3_1 <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.82/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.82/0.79  fof(f1219,plain,(
% 2.82/0.79    sK1 != k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | ~r1_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) | spl3_1),
% 2.82/0.79    inference(superposition,[],[f74,f336])).
% 2.82/0.79  fof(f336,plain,(
% 2.82/0.79    ( ! [X2,X3] : (k5_xboole_0(X3,X2) = k2_xboole_0(X3,X2) | ~r1_xboole_0(X2,X3)) )),
% 2.82/0.79    inference(superposition,[],[f334,f54])).
% 2.82/0.79  fof(f54,plain,(
% 2.82/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.82/0.79    inference(cnf_transformation,[],[f24])).
% 2.82/0.79  fof(f24,plain,(
% 2.82/0.79    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 2.82/0.79    inference(ennf_transformation,[],[f21])).
% 2.82/0.79  fof(f21,plain,(
% 2.82/0.79    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 2.82/0.79    inference(unused_predicate_definition_removal,[],[f7])).
% 2.82/0.79  fof(f7,axiom,(
% 2.82/0.79    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.82/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.82/0.79  fof(f334,plain,(
% 2.82/0.79    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 2.82/0.79    inference(forward_demodulation,[],[f142,f116])).
% 2.82/0.79  fof(f116,plain,(
% 2.82/0.79    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))) )),
% 2.82/0.79    inference(superposition,[],[f48,f49])).
% 2.82/0.79  fof(f142,plain,(
% 2.82/0.79    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3)))) )),
% 2.82/0.79    inference(superposition,[],[f47,f45])).
% 2.82/0.79  fof(f47,plain,(
% 2.82/0.79    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.82/0.79    inference(cnf_transformation,[],[f9])).
% 2.82/0.79  fof(f9,axiom,(
% 2.82/0.79    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.82/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 2.82/0.79  fof(f74,plain,(
% 2.82/0.79    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | spl3_1),
% 2.82/0.79    inference(avatar_component_clause,[],[f72])).
% 2.82/0.79  fof(f659,plain,(
% 2.82/0.79    ~spl3_2 | spl3_16),
% 2.82/0.79    inference(avatar_contradiction_clause,[],[f658])).
% 2.82/0.79  fof(f658,plain,(
% 2.82/0.79    $false | (~spl3_2 | spl3_16)),
% 2.82/0.79    inference(subsumption_resolution,[],[f656,f79])).
% 2.82/0.79  fof(f79,plain,(
% 2.82/0.79    r2_hidden(sK0,sK1) | ~spl3_2),
% 2.82/0.79    inference(avatar_component_clause,[],[f77])).
% 2.82/0.79  fof(f77,plain,(
% 2.82/0.79    spl3_2 <=> r2_hidden(sK0,sK1)),
% 2.82/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.82/0.79  fof(f656,plain,(
% 2.82/0.79    ~r2_hidden(sK0,sK1) | spl3_16),
% 2.82/0.79    inference(resolution,[],[f552,f56])).
% 2.82/0.79  fof(f56,plain,(
% 2.82/0.79    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.82/0.79    inference(cnf_transformation,[],[f35])).
% 2.82/0.79  fof(f35,plain,(
% 2.82/0.79    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.82/0.79    inference(nnf_transformation,[],[f15])).
% 2.82/0.79  fof(f15,axiom,(
% 2.82/0.79    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.82/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.82/0.79  fof(f552,plain,(
% 2.82/0.79    ~r1_tarski(k1_tarski(sK0),sK1) | spl3_16),
% 2.82/0.79    inference(avatar_component_clause,[],[f550])).
% 2.82/0.79  fof(f553,plain,(
% 2.82/0.79    ~spl3_16 | spl3_15),
% 2.82/0.79    inference(avatar_split_clause,[],[f548,f476,f550])).
% 2.82/0.79  fof(f476,plain,(
% 2.82/0.79    spl3_15 <=> r2_hidden(sK0,k3_xboole_0(sK1,k1_tarski(sK0)))),
% 2.82/0.79    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 2.82/0.79  fof(f548,plain,(
% 2.82/0.79    ~r1_tarski(k1_tarski(sK0),sK1) | spl3_15),
% 2.82/0.79    inference(subsumption_resolution,[],[f546,f81])).
% 2.82/0.79  fof(f81,plain,(
% 2.82/0.79    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 2.82/0.79    inference(superposition,[],[f69,f50])).
% 2.82/0.79  fof(f50,plain,(
% 2.82/0.79    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.82/0.79    inference(cnf_transformation,[],[f11])).
% 2.82/0.79  fof(f11,axiom,(
% 2.82/0.79    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.82/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.82/0.79  fof(f69,plain,(
% 2.82/0.79    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 2.82/0.79    inference(equality_resolution,[],[f68])).
% 2.82/0.79  fof(f68,plain,(
% 2.82/0.79    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 2.82/0.79    inference(equality_resolution,[],[f40])).
% 2.82/0.79  fof(f40,plain,(
% 2.82/0.79    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.82/0.79    inference(cnf_transformation,[],[f33])).
% 2.82/0.79  fof(f33,plain,(
% 2.82/0.79    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.82/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 2.82/0.79  fof(f32,plain,(
% 2.82/0.79    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.82/0.79    introduced(choice_axiom,[])).
% 2.82/0.79  fof(f31,plain,(
% 2.82/0.79    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.82/0.79    inference(rectify,[],[f30])).
% 2.82/0.79  fof(f30,plain,(
% 2.82/0.79    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.82/0.79    inference(flattening,[],[f29])).
% 2.82/0.79  fof(f29,plain,(
% 2.82/0.79    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.82/0.79    inference(nnf_transformation,[],[f10])).
% 2.82/0.79  fof(f10,axiom,(
% 2.82/0.79    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.82/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 2.82/0.79  fof(f546,plain,(
% 2.82/0.79    ~r2_hidden(sK0,k1_tarski(sK0)) | ~r1_tarski(k1_tarski(sK0),sK1) | spl3_15),
% 2.82/0.79    inference(superposition,[],[f477,f85])).
% 2.82/0.79  fof(f477,plain,(
% 2.82/0.79    ~r2_hidden(sK0,k3_xboole_0(sK1,k1_tarski(sK0))) | spl3_15),
% 2.82/0.79    inference(avatar_component_clause,[],[f476])).
% 2.82/0.79  fof(f545,plain,(
% 2.82/0.79    ~spl3_15 | ~spl3_2 | ~spl3_14),
% 2.82/0.79    inference(avatar_split_clause,[],[f544,f444,f77,f476])).
% 2.82/0.79  fof(f544,plain,(
% 2.82/0.79    ~r2_hidden(sK0,k3_xboole_0(sK1,k1_tarski(sK0))) | (~spl3_2 | ~spl3_14)),
% 2.82/0.79    inference(subsumption_resolution,[],[f539,f79])).
% 2.82/0.79  fof(f539,plain,(
% 2.82/0.79    ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k3_xboole_0(sK1,k1_tarski(sK0))) | ~spl3_14),
% 2.82/0.79    inference(resolution,[],[f445,f162])).
% 2.82/0.79  fof(f162,plain,(
% 2.82/0.79    ( ! [X4,X2,X3] : (~r2_hidden(X4,k4_xboole_0(X2,X3)) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,k3_xboole_0(X2,X3))) )),
% 2.82/0.79    inference(superposition,[],[f59,f48])).
% 2.82/0.79  fof(f59,plain,(
% 2.82/0.79    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 2.82/0.79    inference(cnf_transformation,[],[f36])).
% 2.82/0.79  fof(f36,plain,(
% 2.82/0.79    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 2.82/0.79    inference(nnf_transformation,[],[f26])).
% 2.82/0.79  fof(f26,plain,(
% 2.82/0.79    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.82/0.79    inference(ennf_transformation,[],[f2])).
% 2.82/0.79  fof(f2,axiom,(
% 2.82/0.79    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.82/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 2.82/0.79  fof(f445,plain,(
% 2.82/0.79    r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK0))) | ~spl3_14),
% 2.82/0.79    inference(avatar_component_clause,[],[f444])).
% 2.82/0.79  fof(f80,plain,(
% 2.82/0.79    spl3_2),
% 2.82/0.79    inference(avatar_split_clause,[],[f37,f77])).
% 2.82/0.79  fof(f37,plain,(
% 2.82/0.79    r2_hidden(sK0,sK1)),
% 2.82/0.79    inference(cnf_transformation,[],[f28])).
% 2.82/0.79  fof(f28,plain,(
% 2.82/0.79    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 2.82/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f27])).
% 2.82/0.79  fof(f27,plain,(
% 2.82/0.79    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 2.82/0.79    introduced(choice_axiom,[])).
% 2.82/0.79  fof(f22,plain,(
% 2.82/0.79    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 2.82/0.79    inference(ennf_transformation,[],[f20])).
% 2.82/0.79  fof(f20,negated_conjecture,(
% 2.82/0.79    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 2.82/0.79    inference(negated_conjecture,[],[f19])).
% 2.82/0.79  fof(f19,conjecture,(
% 2.82/0.79    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 2.82/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 2.82/0.79  fof(f75,plain,(
% 2.82/0.79    ~spl3_1),
% 2.82/0.79    inference(avatar_split_clause,[],[f38,f72])).
% 2.82/0.79  fof(f38,plain,(
% 2.82/0.79    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.82/0.79    inference(cnf_transformation,[],[f28])).
% 2.82/0.79  % SZS output end Proof for theBenchmark
% 2.82/0.79  % (8090)------------------------------
% 2.82/0.79  % (8090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.82/0.79  % (8090)Termination reason: Refutation
% 2.82/0.79  
% 2.82/0.79  % (8090)Memory used [KB]: 7547
% 2.82/0.79  % (8090)Time elapsed: 0.275 s
% 2.82/0.79  % (8090)------------------------------
% 2.82/0.79  % (8090)------------------------------
% 2.82/0.79  % (8066)Success in time 0.428 s
%------------------------------------------------------------------------------
