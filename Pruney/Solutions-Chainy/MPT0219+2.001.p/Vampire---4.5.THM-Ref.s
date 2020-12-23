%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:20 EST 2020

% Result     : Theorem 3.50s
% Output     : Refutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 232 expanded)
%              Number of leaves         :   21 (  80 expanded)
%              Depth                    :   15
%              Number of atoms          :  222 ( 479 expanded)
%              Number of equality atoms :  159 ( 385 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1958,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f102,f196,f1904,f1938,f1957])).

fof(f1957,plain,
    ( spl3_1
    | ~ spl3_33 ),
    inference(avatar_contradiction_clause,[],[f1956])).

fof(f1956,plain,
    ( $false
    | spl3_1
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f1950,f96])).

fof(f96,plain,
    ( sK0 != sK1
    | spl3_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1950,plain,
    ( sK0 = sK1
    | ~ spl3_33 ),
    inference(duplicate_literal_removal,[],[f1945])).

fof(f1945,plain,
    ( sK0 = sK1
    | sK0 = sK1
    | ~ spl3_33 ),
    inference(resolution,[],[f1937,f172])).

fof(f172,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X3))
      | X3 = X5
      | X4 = X5 ) ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X3))
      | X3 = X5
      | X3 = X5
      | X4 = X5 ) ),
    inference(superposition,[],[f92,f75])).

fof(f75,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f41,f70,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f52,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f92,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f53,f69])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f1937,plain,
    ( r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f1935])).

fof(f1935,plain,
    ( spl3_33
  <=> r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f1938,plain,
    ( spl3_33
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f1923,f1899,f1935])).

fof(f1899,plain,
    ( spl3_32
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f1923,plain,
    ( r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_32 ),
    inference(superposition,[],[f87,f1901])).

fof(f1901,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f1899])).

fof(f87,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f56,f69])).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1904,plain,
    ( spl3_32
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f1865,f193,f1899])).

fof(f193,plain,
    ( spl3_6
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f1865,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ spl3_6 ),
    inference(superposition,[],[f195,f271])).

fof(f271,plain,(
    ! [X23,X21,X19,X17,X22,X20,X18,X16] : k6_enumset1(X17,X18,X19,X20,X21,X22,X23,X16) = k5_xboole_0(k6_enumset1(X17,X17,X18,X19,X20,X21,X22,X23),k5_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),k3_xboole_0(k6_enumset1(X17,X17,X18,X19,X20,X21,X22,X23),k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16)))) ),
    inference(superposition,[],[f72,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) ),
    inference(definition_unfolding,[],[f64,f65,f63,f71])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f70])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f195,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f193])).

fof(f196,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f191,f99,f193])).

fof(f99,plain,
    ( spl3_2
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f191,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f101,f40])).

fof(f101,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f102,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f73,f99])).

fof(f73,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f35,f71,f65,f71,f71])).

fof(f35,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f97,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f36,f94])).

fof(f36,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:48:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.51  % (6789)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (6806)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (6797)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (6787)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (6805)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.52  % (6784)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (6784)Refutation not found, incomplete strategy% (6784)------------------------------
% 0.22/0.52  % (6784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6784)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.53  % (6784)Memory used [KB]: 1663
% 0.22/0.53  % (6784)Time elapsed: 0.105 s
% 0.22/0.53  % (6784)------------------------------
% 0.22/0.53  % (6784)------------------------------
% 0.22/0.53  % (6792)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (6790)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (6796)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (6812)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.53  % (6796)Refutation not found, incomplete strategy% (6796)------------------------------
% 0.22/0.53  % (6796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (6796)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (6796)Memory used [KB]: 10618
% 0.22/0.53  % (6796)Time elapsed: 0.104 s
% 0.22/0.53  % (6796)------------------------------
% 0.22/0.53  % (6796)------------------------------
% 0.22/0.53  % (6804)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (6803)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (6785)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (6786)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (6783)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (6810)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (6795)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (6798)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (6798)Refutation not found, incomplete strategy% (6798)------------------------------
% 0.22/0.54  % (6798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (6798)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (6798)Memory used [KB]: 1663
% 0.22/0.54  % (6798)Time elapsed: 0.090 s
% 0.22/0.54  % (6798)------------------------------
% 0.22/0.54  % (6798)------------------------------
% 0.22/0.54  % (6813)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (6813)Refutation not found, incomplete strategy% (6813)------------------------------
% 0.22/0.55  % (6813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (6813)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (6813)Memory used [KB]: 1663
% 0.22/0.55  % (6813)Time elapsed: 0.001 s
% 0.22/0.55  % (6813)------------------------------
% 0.22/0.55  % (6813)------------------------------
% 0.22/0.55  % (6793)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (6810)Refutation not found, incomplete strategy% (6810)------------------------------
% 0.22/0.55  % (6810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (6810)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (6810)Memory used [KB]: 6140
% 0.22/0.55  % (6810)Time elapsed: 0.112 s
% 0.22/0.55  % (6810)------------------------------
% 0.22/0.55  % (6810)------------------------------
% 0.22/0.55  % (6794)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.44/0.55  % (6791)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.44/0.56  % (6802)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.44/0.56  % (6802)Refutation not found, incomplete strategy% (6802)------------------------------
% 1.44/0.56  % (6802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (6802)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (6802)Memory used [KB]: 1663
% 1.44/0.56  % (6802)Time elapsed: 0.139 s
% 1.44/0.56  % (6802)------------------------------
% 1.44/0.56  % (6802)------------------------------
% 1.44/0.56  % (6799)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.44/0.56  % (6808)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.44/0.56  % (6809)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.44/0.56  % (6811)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.44/0.57  % (6801)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.44/0.57  % (6807)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.62/0.59  % (6800)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.62/0.59  % (6800)Refutation not found, incomplete strategy% (6800)------------------------------
% 1.62/0.59  % (6800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (6800)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.59  
% 1.62/0.59  % (6800)Memory used [KB]: 10618
% 1.62/0.59  % (6800)Time elapsed: 0.163 s
% 1.62/0.59  % (6800)------------------------------
% 1.62/0.59  % (6800)------------------------------
% 1.96/0.65  % (6821)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.12/0.65  % (6821)Refutation not found, incomplete strategy% (6821)------------------------------
% 2.12/0.65  % (6821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.66  % (6821)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.66  
% 2.12/0.66  % (6821)Memory used [KB]: 6140
% 2.12/0.66  % (6821)Time elapsed: 0.053 s
% 2.12/0.66  % (6821)------------------------------
% 2.12/0.66  % (6821)------------------------------
% 2.12/0.66  % (6825)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.12/0.67  % (6819)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.12/0.68  % (6818)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.12/0.68  % (6823)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.12/0.68  % (6783)Refutation not found, incomplete strategy% (6783)------------------------------
% 2.12/0.68  % (6783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.68  % (6783)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.68  
% 2.12/0.68  % (6783)Memory used [KB]: 1663
% 2.12/0.68  % (6783)Time elapsed: 0.255 s
% 2.12/0.68  % (6783)------------------------------
% 2.12/0.68  % (6783)------------------------------
% 2.12/0.69  % (6828)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.12/0.70  % (6799)Refutation not found, incomplete strategy% (6799)------------------------------
% 2.12/0.70  % (6799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.70  % (6799)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.70  
% 2.12/0.70  % (6799)Memory used [KB]: 6140
% 2.12/0.70  % (6799)Time elapsed: 0.280 s
% 2.12/0.70  % (6799)------------------------------
% 2.12/0.70  % (6799)------------------------------
% 2.12/0.70  % (6823)Refutation not found, incomplete strategy% (6823)------------------------------
% 2.12/0.70  % (6823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.70  % (6823)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.70  
% 2.12/0.70  % (6823)Memory used [KB]: 10746
% 2.12/0.70  % (6823)Time elapsed: 0.122 s
% 2.12/0.70  % (6823)------------------------------
% 2.12/0.70  % (6823)------------------------------
% 2.12/0.70  % (6829)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.12/0.71  % (6786)Refutation not found, incomplete strategy% (6786)------------------------------
% 2.12/0.71  % (6786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.71  % (6792)Refutation not found, incomplete strategy% (6792)------------------------------
% 2.12/0.71  % (6792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.71  % (6792)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.71  
% 2.12/0.71  % (6792)Memory used [KB]: 6140
% 2.12/0.71  % (6792)Time elapsed: 0.278 s
% 2.12/0.71  % (6792)------------------------------
% 2.12/0.71  % (6792)------------------------------
% 2.12/0.71  % (6786)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.71  
% 2.12/0.71  % (6786)Memory used [KB]: 6140
% 2.12/0.71  % (6786)Time elapsed: 0.288 s
% 2.12/0.71  % (6786)------------------------------
% 2.12/0.71  % (6786)------------------------------
% 2.86/0.77  % (6836)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.86/0.81  % (6837)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.86/0.83  % (6808)Time limit reached!
% 2.86/0.83  % (6808)------------------------------
% 2.86/0.83  % (6808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.86/0.83  % (6808)Termination reason: Time limit
% 2.86/0.83  % (6808)Termination phase: Saturation
% 2.86/0.83  
% 2.86/0.83  % (6808)Memory used [KB]: 13176
% 2.86/0.83  % (6808)Time elapsed: 0.400 s
% 2.86/0.83  % (6808)------------------------------
% 2.86/0.83  % (6808)------------------------------
% 2.86/0.83  % (6838)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.86/0.83  % (6838)Refutation not found, incomplete strategy% (6838)------------------------------
% 2.86/0.83  % (6838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.86/0.83  % (6838)Termination reason: Refutation not found, incomplete strategy
% 2.86/0.83  
% 2.86/0.83  % (6838)Memory used [KB]: 10746
% 2.86/0.83  % (6838)Time elapsed: 0.104 s
% 2.86/0.83  % (6838)------------------------------
% 2.86/0.83  % (6838)------------------------------
% 2.86/0.83  % (6841)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.86/0.84  % (6839)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.86/0.84  % (6840)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 3.32/0.85  % (6785)Time limit reached!
% 3.32/0.85  % (6785)------------------------------
% 3.32/0.85  % (6785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.32/0.85  % (6785)Termination reason: Time limit
% 3.32/0.85  
% 3.32/0.85  % (6785)Memory used [KB]: 6652
% 3.32/0.85  % (6785)Time elapsed: 0.418 s
% 3.32/0.85  % (6785)------------------------------
% 3.32/0.85  % (6785)------------------------------
% 3.50/0.90  % (6819)Refutation found. Thanks to Tanya!
% 3.50/0.90  % SZS status Theorem for theBenchmark
% 3.50/0.90  % SZS output start Proof for theBenchmark
% 3.50/0.90  fof(f1958,plain,(
% 3.50/0.90    $false),
% 3.50/0.90    inference(avatar_sat_refutation,[],[f97,f102,f196,f1904,f1938,f1957])).
% 3.50/0.90  fof(f1957,plain,(
% 3.50/0.90    spl3_1 | ~spl3_33),
% 3.50/0.90    inference(avatar_contradiction_clause,[],[f1956])).
% 3.50/0.90  fof(f1956,plain,(
% 3.50/0.90    $false | (spl3_1 | ~spl3_33)),
% 3.50/0.90    inference(subsumption_resolution,[],[f1950,f96])).
% 3.50/0.90  fof(f96,plain,(
% 3.50/0.90    sK0 != sK1 | spl3_1),
% 3.50/0.90    inference(avatar_component_clause,[],[f94])).
% 3.50/0.90  fof(f94,plain,(
% 3.50/0.90    spl3_1 <=> sK0 = sK1),
% 3.50/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 3.50/0.90  fof(f1950,plain,(
% 3.50/0.90    sK0 = sK1 | ~spl3_33),
% 3.50/0.90    inference(duplicate_literal_removal,[],[f1945])).
% 3.50/0.90  fof(f1945,plain,(
% 3.50/0.90    sK0 = sK1 | sK0 = sK1 | ~spl3_33),
% 3.50/0.90    inference(resolution,[],[f1937,f172])).
% 3.50/0.90  fof(f172,plain,(
% 3.50/0.90    ( ! [X4,X5,X3] : (~r2_hidden(X5,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X3)) | X3 = X5 | X4 = X5) )),
% 3.50/0.90    inference(duplicate_literal_removal,[],[f171])).
% 3.50/0.90  fof(f171,plain,(
% 3.50/0.90    ( ! [X4,X5,X3] : (~r2_hidden(X5,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X3)) | X3 = X5 | X3 = X5 | X4 = X5) )),
% 3.50/0.90    inference(superposition,[],[f92,f75])).
% 3.50/0.90  fof(f75,plain,(
% 3.50/0.90    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 3.50/0.90    inference(definition_unfolding,[],[f41,f70,f70])).
% 3.50/0.90  fof(f70,plain,(
% 3.50/0.90    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.50/0.90    inference(definition_unfolding,[],[f43,f69])).
% 3.50/0.90  fof(f69,plain,(
% 3.50/0.90    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.50/0.90    inference(definition_unfolding,[],[f50,f68])).
% 3.50/0.90  fof(f68,plain,(
% 3.50/0.90    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.50/0.90    inference(definition_unfolding,[],[f52,f67])).
% 3.50/0.90  fof(f67,plain,(
% 3.50/0.90    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.50/0.90    inference(definition_unfolding,[],[f61,f66])).
% 3.50/0.90  fof(f66,plain,(
% 3.50/0.90    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.50/0.90    inference(definition_unfolding,[],[f62,f63])).
% 3.50/0.90  fof(f63,plain,(
% 3.50/0.90    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.50/0.90    inference(cnf_transformation,[],[f19])).
% 3.50/0.90  fof(f19,axiom,(
% 3.50/0.90    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.50/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 3.50/0.90  fof(f62,plain,(
% 3.50/0.90    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.50/0.90    inference(cnf_transformation,[],[f18])).
% 3.50/0.90  fof(f18,axiom,(
% 3.50/0.90    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.50/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 3.50/0.90  fof(f61,plain,(
% 3.50/0.90    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.50/0.90    inference(cnf_transformation,[],[f17])).
% 3.50/0.90  fof(f17,axiom,(
% 3.50/0.90    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.50/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 3.50/0.90  fof(f52,plain,(
% 3.50/0.90    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.50/0.90    inference(cnf_transformation,[],[f16])).
% 3.50/0.90  fof(f16,axiom,(
% 3.50/0.90    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.50/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 3.50/0.90  fof(f50,plain,(
% 3.50/0.90    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.50/0.90    inference(cnf_transformation,[],[f15])).
% 3.50/0.90  fof(f15,axiom,(
% 3.50/0.90    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.50/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 3.50/0.90  fof(f43,plain,(
% 3.50/0.90    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.50/0.90    inference(cnf_transformation,[],[f14])).
% 3.50/0.90  fof(f14,axiom,(
% 3.50/0.90    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.50/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.50/0.90  fof(f41,plain,(
% 3.50/0.90    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.50/0.90    inference(cnf_transformation,[],[f10])).
% 3.50/0.90  fof(f10,axiom,(
% 3.50/0.90    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.50/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.50/0.90  fof(f92,plain,(
% 3.50/0.90    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 3.50/0.90    inference(equality_resolution,[],[f83])).
% 3.50/0.90  fof(f83,plain,(
% 3.50/0.90    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.50/0.90    inference(definition_unfolding,[],[f53,f69])).
% 3.50/0.90  fof(f53,plain,(
% 3.50/0.90    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.50/0.90    inference(cnf_transformation,[],[f34])).
% 3.50/0.90  fof(f34,plain,(
% 3.50/0.90    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.50/0.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 3.50/0.90  fof(f33,plain,(
% 3.50/0.90    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 3.50/0.90    introduced(choice_axiom,[])).
% 3.50/0.90  fof(f32,plain,(
% 3.50/0.90    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.50/0.90    inference(rectify,[],[f31])).
% 3.50/0.90  fof(f31,plain,(
% 3.50/0.90    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.50/0.90    inference(flattening,[],[f30])).
% 3.50/0.90  fof(f30,plain,(
% 3.50/0.90    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.50/0.90    inference(nnf_transformation,[],[f25])).
% 3.50/0.90  fof(f25,plain,(
% 3.50/0.90    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.50/0.90    inference(ennf_transformation,[],[f11])).
% 3.50/0.90  fof(f11,axiom,(
% 3.50/0.90    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.50/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 3.50/0.90  fof(f1937,plain,(
% 3.50/0.90    r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl3_33),
% 3.50/0.90    inference(avatar_component_clause,[],[f1935])).
% 3.50/0.90  fof(f1935,plain,(
% 3.50/0.90    spl3_33 <=> r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 3.50/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 3.50/0.90  fof(f1938,plain,(
% 3.50/0.90    spl3_33 | ~spl3_32),
% 3.50/0.90    inference(avatar_split_clause,[],[f1923,f1899,f1935])).
% 3.50/0.90  fof(f1899,plain,(
% 3.50/0.90    spl3_32 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 3.50/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 3.50/0.90  fof(f1923,plain,(
% 3.50/0.90    r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl3_32),
% 3.50/0.90    inference(superposition,[],[f87,f1901])).
% 3.50/0.90  fof(f1901,plain,(
% 3.50/0.90    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | ~spl3_32),
% 3.50/0.90    inference(avatar_component_clause,[],[f1899])).
% 3.50/0.90  fof(f87,plain,(
% 3.50/0.90    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 3.50/0.90    inference(equality_resolution,[],[f86])).
% 3.50/0.90  fof(f86,plain,(
% 3.50/0.90    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 3.50/0.90    inference(equality_resolution,[],[f80])).
% 3.50/0.90  fof(f80,plain,(
% 3.50/0.90    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 3.50/0.90    inference(definition_unfolding,[],[f56,f69])).
% 3.50/0.90  fof(f56,plain,(
% 3.50/0.90    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.50/0.90    inference(cnf_transformation,[],[f34])).
% 3.50/0.90  fof(f1904,plain,(
% 3.50/0.90    spl3_32 | ~spl3_6),
% 3.50/0.90    inference(avatar_split_clause,[],[f1865,f193,f1899])).
% 3.50/0.90  fof(f193,plain,(
% 3.50/0.90    spl3_6 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 3.50/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 3.50/0.90  fof(f1865,plain,(
% 3.50/0.90    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | ~spl3_6),
% 3.50/0.90    inference(superposition,[],[f195,f271])).
% 3.50/0.90  fof(f271,plain,(
% 3.50/0.90    ( ! [X23,X21,X19,X17,X22,X20,X18,X16] : (k6_enumset1(X17,X18,X19,X20,X21,X22,X23,X16) = k5_xboole_0(k6_enumset1(X17,X17,X18,X19,X20,X21,X22,X23),k5_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),k3_xboole_0(k6_enumset1(X17,X17,X18,X19,X20,X21,X22,X23),k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16))))) )),
% 3.50/0.90    inference(superposition,[],[f72,f40])).
% 3.50/0.90  fof(f40,plain,(
% 3.50/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.50/0.90    inference(cnf_transformation,[],[f1])).
% 3.50/0.90  fof(f1,axiom,(
% 3.50/0.90    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.50/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.50/0.90  fof(f72,plain,(
% 3.50/0.90    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))))) )),
% 3.50/0.90    inference(definition_unfolding,[],[f64,f65,f63,f71])).
% 3.50/0.90  fof(f71,plain,(
% 3.50/0.90    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.50/0.90    inference(definition_unfolding,[],[f38,f70])).
% 3.50/0.90  fof(f38,plain,(
% 3.50/0.90    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.50/0.90    inference(cnf_transformation,[],[f13])).
% 3.50/0.90  fof(f13,axiom,(
% 3.50/0.90    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.50/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 3.50/0.90  fof(f65,plain,(
% 3.50/0.90    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.50/0.90    inference(definition_unfolding,[],[f45,f44])).
% 3.50/0.90  fof(f44,plain,(
% 3.50/0.90    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.50/0.90    inference(cnf_transformation,[],[f5])).
% 3.50/0.90  fof(f5,axiom,(
% 3.50/0.90    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.50/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.50/0.90  fof(f45,plain,(
% 3.50/0.90    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.50/0.90    inference(cnf_transformation,[],[f9])).
% 3.50/0.90  fof(f9,axiom,(
% 3.50/0.90    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.50/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 3.50/0.90  fof(f64,plain,(
% 3.50/0.90    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 3.50/0.90    inference(cnf_transformation,[],[f12])).
% 3.50/0.90  fof(f12,axiom,(
% 3.50/0.90    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 3.50/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
% 3.50/0.90  fof(f195,plain,(
% 3.50/0.90    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | ~spl3_6),
% 3.50/0.90    inference(avatar_component_clause,[],[f193])).
% 3.50/0.90  fof(f196,plain,(
% 3.50/0.90    spl3_6 | ~spl3_2),
% 3.50/0.90    inference(avatar_split_clause,[],[f191,f99,f193])).
% 3.50/0.90  fof(f99,plain,(
% 3.50/0.90    spl3_2 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 3.50/0.90    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 3.50/0.90  fof(f191,plain,(
% 3.50/0.90    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | ~spl3_2),
% 3.50/0.90    inference(forward_demodulation,[],[f101,f40])).
% 3.50/0.90  fof(f101,plain,(
% 3.50/0.90    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~spl3_2),
% 3.50/0.90    inference(avatar_component_clause,[],[f99])).
% 3.50/0.90  fof(f102,plain,(
% 3.50/0.90    spl3_2),
% 3.50/0.90    inference(avatar_split_clause,[],[f73,f99])).
% 3.50/0.90  fof(f73,plain,(
% 3.50/0.90    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 3.50/0.91    inference(definition_unfolding,[],[f35,f71,f65,f71,f71])).
% 3.50/0.91  fof(f35,plain,(
% 3.50/0.91    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 3.50/0.91    inference(cnf_transformation,[],[f27])).
% 3.50/0.91  fof(f27,plain,(
% 3.50/0.91    sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 3.50/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26])).
% 3.50/0.91  fof(f26,plain,(
% 3.50/0.91    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 3.50/0.91    introduced(choice_axiom,[])).
% 3.50/0.91  fof(f23,plain,(
% 3.50/0.91    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 3.50/0.91    inference(ennf_transformation,[],[f21])).
% 3.50/0.91  fof(f21,negated_conjecture,(
% 3.50/0.91    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 3.50/0.91    inference(negated_conjecture,[],[f20])).
% 3.50/0.91  fof(f20,conjecture,(
% 3.50/0.91    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 3.50/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 3.50/0.91  fof(f97,plain,(
% 3.50/0.91    ~spl3_1),
% 3.50/0.91    inference(avatar_split_clause,[],[f36,f94])).
% 3.50/0.91  fof(f36,plain,(
% 3.50/0.91    sK0 != sK1),
% 3.50/0.91    inference(cnf_transformation,[],[f27])).
% 3.50/0.91  % SZS output end Proof for theBenchmark
% 3.50/0.91  % (6819)------------------------------
% 3.50/0.91  % (6819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.50/0.91  % (6819)Termination reason: Refutation
% 3.50/0.91  
% 3.50/0.91  % (6819)Memory used [KB]: 12920
% 3.50/0.91  % (6819)Time elapsed: 0.325 s
% 3.50/0.91  % (6819)------------------------------
% 3.50/0.91  % (6819)------------------------------
% 3.50/0.91  % (6780)Success in time 0.525 s
%------------------------------------------------------------------------------
