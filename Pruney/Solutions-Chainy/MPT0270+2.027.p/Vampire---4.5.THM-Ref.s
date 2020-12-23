%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:00 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 510 expanded)
%              Number of leaves         :   17 ( 150 expanded)
%              Depth                    :   18
%              Number of atoms          :  274 (2132 expanded)
%              Number of equality atoms :   66 ( 306 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f572,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f98,f510,f561])).

fof(f561,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f560])).

fof(f560,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f556,f96])).

fof(f96,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_2
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f556,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ spl6_1 ),
    inference(trivial_inequality_removal,[],[f541])).

fof(f541,plain,
    ( sK3 != sK3
    | ~ r2_hidden(sK2,sK3)
    | ~ spl6_1 ),
    inference(superposition,[],[f79,f534])).

fof(f534,plain,
    ( sK3 = k4_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f533,f435])).

fof(f435,plain,(
    ! [X3] : k5_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(backward_demodulation,[],[f164,f420])).

fof(f420,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(resolution,[],[f411,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f17])).

fof(f17,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f411,plain,(
    ! [X12] : sP0(k1_xboole_0,X12,X12) ),
    inference(resolution,[],[f373,f171])).

fof(f171,plain,(
    ! [X10] : ~ r2_hidden(X10,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f168,f123])).

fof(f123,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f55,f108])).

fof(f108,plain,(
    ! [X0] : sP0(X0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f84,f107])).

fof(f107,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f102,f43])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f102,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f50,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f84,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f168,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X10,k1_xboole_0)
      | r2_hidden(X10,X9) ) ),
    inference(superposition,[],[f119,f150])).

fof(f150,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)) ),
    inference(resolution,[],[f134,f102])).

fof(f134,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) ),
    inference(superposition,[],[f43,f77])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f44,f46,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f54,f84])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f373,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK4(X5,X6,X6),X5)
      | sP0(X5,X6,X6) ) ),
    inference(subsumption_resolution,[],[f371,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f371,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK4(X5,X6,X6),X5)
      | ~ r2_hidden(sK4(X5,X6,X6),X6)
      | sP0(X5,X6,X6) ) ),
    inference(duplicate_literal_removal,[],[f366])).

fof(f366,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK4(X5,X6,X6),X5)
      | ~ r2_hidden(sK4(X5,X6,X6),X6)
      | sP0(X5,X6,X6)
      | sP0(X5,X6,X6) ) ),
    inference(resolution,[],[f59,f272])).

fof(f272,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),X1)
      | sP0(X0,X1,X1) ) ),
    inference(factoring,[],[f57])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f164,plain,(
    ! [X3] : k4_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f74,f150])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f47,f46])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f533,plain,
    ( k4_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = k5_xboole_0(sK3,k1_xboole_0)
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f522,f316])).

fof(f316,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(X6,X6) ),
    inference(resolution,[],[f308,f61])).

fof(f308,plain,(
    ! [X10] : sP0(X10,X10,k1_xboole_0) ),
    inference(resolution,[],[f302,f171])).

fof(f302,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(X2,X2,X3),X3)
      | sP0(X2,X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f296])).

fof(f296,plain,(
    ! [X2,X3] :
      ( sP0(X2,X2,X3)
      | r2_hidden(sK4(X2,X2,X3),X3)
      | r2_hidden(sK4(X2,X2,X3),X3)
      | sP0(X2,X2,X3) ) ),
    inference(resolution,[],[f58,f57])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | sP0(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f522,plain,
    ( k4_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = k5_xboole_0(sK3,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)))
    | ~ spl6_1 ),
    inference(superposition,[],[f133,f91])).

fof(f91,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_1
  <=> k2_enumset1(sK2,sK2,sK2,sK2) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f133,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f74,f77])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f51,f73])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f510,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f509])).

fof(f509,plain,
    ( $false
    | spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f508,f117])).

fof(f117,plain,
    ( ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | spl6_1 ),
    inference(subsumption_resolution,[],[f115,f43])).

fof(f115,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | spl6_1 ),
    inference(extensionality_resolution,[],[f50,f92])).

fof(f92,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f508,plain,
    ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | spl6_2 ),
    inference(forward_demodulation,[],[f507,f420])).

fof(f507,plain,
    ( r1_tarski(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k1_xboole_0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | spl6_2 ),
    inference(forward_demodulation,[],[f492,f316])).

fof(f492,plain,
    ( r1_tarski(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(sK3,sK3)),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | spl6_2 ),
    inference(superposition,[],[f152,f172])).

fof(f172,plain,
    ( sK3 = k4_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2))
    | spl6_2 ),
    inference(resolution,[],[f78,f95])).

fof(f95,plain,
    ( ~ r2_hidden(sK2,sK3)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f52,f73])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f152,plain,(
    ! [X2,X1] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f134,f77])).

fof(f98,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f76,f94,f90])).

fof(f76,plain,
    ( ~ r2_hidden(sK2,sK3)
    | k2_enumset1(sK2,sK2,sK2,sK2) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f39,f73,f73])).

fof(f39,plain,
    ( ~ r2_hidden(sK2,sK3)
    | k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( r2_hidden(sK2,sK3)
      | k1_tarski(sK2) != k4_xboole_0(k1_tarski(sK2),sK3) )
    & ( ~ r2_hidden(sK2,sK3)
      | k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
        & ( ~ r2_hidden(X0,X1)
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( r2_hidden(sK2,sK3)
        | k1_tarski(sK2) != k4_xboole_0(k1_tarski(sK2),sK3) )
      & ( ~ r2_hidden(sK2,sK3)
        | k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f97,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f75,f94,f90])).

fof(f75,plain,
    ( r2_hidden(sK2,sK3)
    | k2_enumset1(sK2,sK2,sK2,sK2) != k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f40,f73,f73])).

fof(f40,plain,
    ( r2_hidden(sK2,sK3)
    | k1_tarski(sK2) != k4_xboole_0(k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:22:59 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (2479)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (2501)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (2495)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (2477)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (2499)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.53  % (2493)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (2498)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (2483)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (2481)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (2478)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (2492)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (2491)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (2497)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (2484)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (2491)Refutation not found, incomplete strategy% (2491)------------------------------
% 0.22/0.54  % (2491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2491)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (2491)Memory used [KB]: 10618
% 0.22/0.54  % (2491)Time elapsed: 0.124 s
% 0.22/0.54  % (2491)------------------------------
% 0.22/0.54  % (2491)------------------------------
% 0.22/0.55  % (2482)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (2486)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (2475)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (2480)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (2500)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (2502)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (2487)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (2504)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (2476)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.55  % (2504)Refutation not found, incomplete strategy% (2504)------------------------------
% 0.22/0.55  % (2504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (2504)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (2504)Memory used [KB]: 1663
% 0.22/0.55  % (2504)Time elapsed: 0.001 s
% 0.22/0.55  % (2504)------------------------------
% 0.22/0.55  % (2504)------------------------------
% 0.22/0.55  % (2476)Refutation not found, incomplete strategy% (2476)------------------------------
% 0.22/0.55  % (2476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (2476)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (2476)Memory used [KB]: 1663
% 0.22/0.55  % (2476)Time elapsed: 0.131 s
% 0.22/0.55  % (2476)------------------------------
% 0.22/0.55  % (2476)------------------------------
% 0.22/0.56  % (2489)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (2503)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  % (2494)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.56  % (2496)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.56  % (2488)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (2503)Refutation not found, incomplete strategy% (2503)------------------------------
% 0.22/0.56  % (2503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (2503)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (2503)Memory used [KB]: 10746
% 0.22/0.56  % (2503)Time elapsed: 0.136 s
% 0.22/0.56  % (2503)------------------------------
% 0.22/0.56  % (2503)------------------------------
% 1.43/0.56  % (2490)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.43/0.57  % (2485)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.43/0.58  % (2485)Refutation not found, incomplete strategy% (2485)------------------------------
% 1.43/0.58  % (2485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (2485)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  
% 1.63/0.58  % (2485)Memory used [KB]: 10746
% 1.63/0.58  % (2485)Time elapsed: 0.157 s
% 1.63/0.58  % (2485)------------------------------
% 1.63/0.58  % (2485)------------------------------
% 1.63/0.58  % (2481)Refutation found. Thanks to Tanya!
% 1.63/0.58  % SZS status Theorem for theBenchmark
% 1.63/0.58  % SZS output start Proof for theBenchmark
% 1.63/0.58  fof(f572,plain,(
% 1.63/0.58    $false),
% 1.63/0.58    inference(avatar_sat_refutation,[],[f97,f98,f510,f561])).
% 1.63/0.58  fof(f561,plain,(
% 1.63/0.58    ~spl6_1 | ~spl6_2),
% 1.63/0.58    inference(avatar_contradiction_clause,[],[f560])).
% 1.63/0.58  fof(f560,plain,(
% 1.63/0.58    $false | (~spl6_1 | ~spl6_2)),
% 1.63/0.58    inference(subsumption_resolution,[],[f556,f96])).
% 1.63/0.58  fof(f96,plain,(
% 1.63/0.58    r2_hidden(sK2,sK3) | ~spl6_2),
% 1.63/0.58    inference(avatar_component_clause,[],[f94])).
% 1.63/0.58  fof(f94,plain,(
% 1.63/0.58    spl6_2 <=> r2_hidden(sK2,sK3)),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.63/0.58  fof(f556,plain,(
% 1.63/0.58    ~r2_hidden(sK2,sK3) | ~spl6_1),
% 1.63/0.58    inference(trivial_inequality_removal,[],[f541])).
% 1.63/0.58  fof(f541,plain,(
% 1.63/0.58    sK3 != sK3 | ~r2_hidden(sK2,sK3) | ~spl6_1),
% 1.63/0.58    inference(superposition,[],[f79,f534])).
% 1.63/0.58  fof(f534,plain,(
% 1.63/0.58    sK3 = k4_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) | ~spl6_1),
% 1.63/0.58    inference(forward_demodulation,[],[f533,f435])).
% 1.63/0.58  fof(f435,plain,(
% 1.63/0.58    ( ! [X3] : (k5_xboole_0(X3,k1_xboole_0) = X3) )),
% 1.63/0.58    inference(backward_demodulation,[],[f164,f420])).
% 1.63/0.58  fof(f420,plain,(
% 1.63/0.58    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6) )),
% 1.63/0.58    inference(resolution,[],[f411,f61])).
% 1.63/0.58  fof(f61,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.63/0.58    inference(cnf_transformation,[],[f32])).
% 1.63/0.58  fof(f32,plain,(
% 1.63/0.58    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.63/0.58    inference(nnf_transformation,[],[f18])).
% 1.63/0.58  fof(f18,plain,(
% 1.63/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.63/0.58    inference(definition_folding,[],[f2,f17])).
% 1.63/0.58  fof(f17,plain,(
% 1.63/0.58    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.63/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.63/0.58  fof(f2,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.63/0.58  fof(f411,plain,(
% 1.63/0.58    ( ! [X12] : (sP0(k1_xboole_0,X12,X12)) )),
% 1.63/0.58    inference(resolution,[],[f373,f171])).
% 1.63/0.58  fof(f171,plain,(
% 1.63/0.58    ( ! [X10] : (~r2_hidden(X10,k1_xboole_0)) )),
% 1.63/0.58    inference(subsumption_resolution,[],[f168,f123])).
% 1.63/0.58  fof(f123,plain,(
% 1.63/0.58    ( ! [X4,X3] : (~r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,X4)) )),
% 1.63/0.58    inference(resolution,[],[f55,f108])).
% 1.63/0.58  fof(f108,plain,(
% 1.63/0.58    ( ! [X0] : (sP0(X0,k1_xboole_0,k1_xboole_0)) )),
% 1.63/0.58    inference(superposition,[],[f84,f107])).
% 1.63/0.58  fof(f107,plain,(
% 1.63/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.63/0.58    inference(resolution,[],[f102,f43])).
% 1.63/0.58  fof(f43,plain,(
% 1.63/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f6])).
% 1.63/0.58  fof(f6,axiom,(
% 1.63/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.63/0.58  fof(f102,plain,(
% 1.63/0.58    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.63/0.58    inference(resolution,[],[f50,f41])).
% 1.63/0.58  fof(f41,plain,(
% 1.63/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f5])).
% 1.63/0.58  fof(f5,axiom,(
% 1.63/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.63/0.58  fof(f50,plain,(
% 1.63/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f25])).
% 1.63/0.58  fof(f25,plain,(
% 1.63/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.63/0.58    inference(flattening,[],[f24])).
% 1.63/0.58  fof(f24,plain,(
% 1.63/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.63/0.58    inference(nnf_transformation,[],[f3])).
% 1.63/0.58  fof(f3,axiom,(
% 1.63/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.63/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.63/0.58  fof(f84,plain,(
% 1.63/0.58    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 1.63/0.58    inference(equality_resolution,[],[f60])).
% 1.63/0.58  fof(f60,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.63/0.58    inference(cnf_transformation,[],[f32])).
% 1.63/0.58  fof(f55,plain,(
% 1.63/0.58    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f31])).
% 1.63/0.58  fof(f31,plain,(
% 1.63/0.58    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.63/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 1.63/0.58  fof(f30,plain,(
% 1.63/0.58    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.63/0.58    introduced(choice_axiom,[])).
% 1.63/0.58  fof(f29,plain,(
% 1.63/0.58    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.63/0.58    inference(rectify,[],[f28])).
% 1.63/0.58  fof(f28,plain,(
% 1.63/0.58    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.63/0.58    inference(flattening,[],[f27])).
% 1.63/0.58  fof(f27,plain,(
% 1.63/0.58    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.63/0.58    inference(nnf_transformation,[],[f17])).
% 1.63/0.58  fof(f168,plain,(
% 1.63/0.58    ( ! [X10,X9] : (~r2_hidden(X10,k1_xboole_0) | r2_hidden(X10,X9)) )),
% 1.63/0.58    inference(superposition,[],[f119,f150])).
% 1.63/0.58  fof(f150,plain,(
% 1.63/0.58    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))) )),
% 1.63/0.58    inference(resolution,[],[f134,f102])).
% 1.63/0.59  fof(f134,plain,(
% 1.63/0.59    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)) )),
% 1.63/0.59    inference(superposition,[],[f43,f77])).
% 1.63/0.59  fof(f77,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.63/0.59    inference(definition_unfolding,[],[f44,f46,f46])).
% 1.63/0.59  fof(f46,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.63/0.59    inference(cnf_transformation,[],[f7])).
% 1.63/0.59  fof(f7,axiom,(
% 1.63/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.63/0.59  fof(f44,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f1])).
% 1.63/0.59  fof(f1,axiom,(
% 1.63/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.63/0.59  fof(f119,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | r2_hidden(X0,X1)) )),
% 1.63/0.59    inference(resolution,[],[f54,f84])).
% 1.63/0.59  fof(f54,plain,(
% 1.63/0.59    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f31])).
% 1.63/0.59  fof(f373,plain,(
% 1.63/0.59    ( ! [X6,X5] : (r2_hidden(sK4(X5,X6,X6),X5) | sP0(X5,X6,X6)) )),
% 1.63/0.59    inference(subsumption_resolution,[],[f371,f57])).
% 1.63/0.59  fof(f57,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f31])).
% 1.63/0.59  fof(f371,plain,(
% 1.63/0.59    ( ! [X6,X5] : (r2_hidden(sK4(X5,X6,X6),X5) | ~r2_hidden(sK4(X5,X6,X6),X6) | sP0(X5,X6,X6)) )),
% 1.63/0.59    inference(duplicate_literal_removal,[],[f366])).
% 1.63/0.59  fof(f366,plain,(
% 1.63/0.59    ( ! [X6,X5] : (r2_hidden(sK4(X5,X6,X6),X5) | ~r2_hidden(sK4(X5,X6,X6),X6) | sP0(X5,X6,X6) | sP0(X5,X6,X6)) )),
% 1.63/0.59    inference(resolution,[],[f59,f272])).
% 1.63/0.59  fof(f272,plain,(
% 1.63/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X1),X1) | sP0(X0,X1,X1)) )),
% 1.63/0.59    inference(factoring,[],[f57])).
% 1.63/0.59  fof(f59,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f31])).
% 1.63/0.59  fof(f164,plain,(
% 1.63/0.59    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X3,k1_xboole_0)) )),
% 1.63/0.59    inference(superposition,[],[f74,f150])).
% 1.63/0.59  fof(f74,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.63/0.59    inference(definition_unfolding,[],[f47,f46])).
% 1.63/0.59  fof(f47,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.63/0.59    inference(cnf_transformation,[],[f4])).
% 1.63/0.59  fof(f4,axiom,(
% 1.63/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.63/0.59  fof(f533,plain,(
% 1.63/0.59    k4_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = k5_xboole_0(sK3,k1_xboole_0) | ~spl6_1),
% 1.63/0.59    inference(forward_demodulation,[],[f522,f316])).
% 1.63/0.59  fof(f316,plain,(
% 1.63/0.59    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(X6,X6)) )),
% 1.63/0.59    inference(resolution,[],[f308,f61])).
% 1.63/0.59  fof(f308,plain,(
% 1.63/0.59    ( ! [X10] : (sP0(X10,X10,k1_xboole_0)) )),
% 1.63/0.59    inference(resolution,[],[f302,f171])).
% 1.63/0.59  fof(f302,plain,(
% 1.63/0.59    ( ! [X2,X3] : (r2_hidden(sK4(X2,X2,X3),X3) | sP0(X2,X2,X3)) )),
% 1.63/0.59    inference(duplicate_literal_removal,[],[f296])).
% 1.63/0.59  fof(f296,plain,(
% 1.63/0.59    ( ! [X2,X3] : (sP0(X2,X2,X3) | r2_hidden(sK4(X2,X2,X3),X3) | r2_hidden(sK4(X2,X2,X3),X3) | sP0(X2,X2,X3)) )),
% 1.63/0.59    inference(resolution,[],[f58,f57])).
% 1.63/0.59  fof(f58,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | sP0(X0,X1,X2) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f31])).
% 1.63/0.59  fof(f522,plain,(
% 1.63/0.59    k4_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = k5_xboole_0(sK3,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2))) | ~spl6_1),
% 1.63/0.59    inference(superposition,[],[f133,f91])).
% 1.63/0.59  fof(f91,plain,(
% 1.63/0.59    k2_enumset1(sK2,sK2,sK2,sK2) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3) | ~spl6_1),
% 1.63/0.59    inference(avatar_component_clause,[],[f90])).
% 1.63/0.59  fof(f90,plain,(
% 1.63/0.59    spl6_1 <=> k2_enumset1(sK2,sK2,sK2,sK2) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.63/0.59  fof(f133,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.63/0.59    inference(superposition,[],[f74,f77])).
% 1.63/0.59  fof(f79,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 1.63/0.59    inference(definition_unfolding,[],[f51,f73])).
% 1.63/0.59  fof(f73,plain,(
% 1.63/0.59    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.63/0.59    inference(definition_unfolding,[],[f42,f72])).
% 1.63/0.59  fof(f72,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.63/0.59    inference(definition_unfolding,[],[f45,f53])).
% 1.63/0.59  fof(f53,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f11])).
% 1.63/0.59  fof(f11,axiom,(
% 1.63/0.59    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.63/0.59  fof(f45,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f10])).
% 1.63/0.59  fof(f10,axiom,(
% 1.63/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.63/0.59  fof(f42,plain,(
% 1.63/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f9])).
% 1.63/0.59  fof(f9,axiom,(
% 1.63/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.63/0.59  fof(f51,plain,(
% 1.63/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.63/0.59    inference(cnf_transformation,[],[f26])).
% 1.63/0.59  fof(f26,plain,(
% 1.63/0.59    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.63/0.59    inference(nnf_transformation,[],[f12])).
% 1.63/0.59  fof(f12,axiom,(
% 1.63/0.59    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.63/0.59  fof(f510,plain,(
% 1.63/0.59    spl6_1 | spl6_2),
% 1.63/0.59    inference(avatar_contradiction_clause,[],[f509])).
% 1.63/0.59  fof(f509,plain,(
% 1.63/0.59    $false | (spl6_1 | spl6_2)),
% 1.63/0.59    inference(subsumption_resolution,[],[f508,f117])).
% 1.63/0.59  fof(f117,plain,(
% 1.63/0.59    ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) | spl6_1),
% 1.63/0.59    inference(subsumption_resolution,[],[f115,f43])).
% 1.63/0.59  fof(f115,plain,(
% 1.63/0.59    ~r1_tarski(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3),k2_enumset1(sK2,sK2,sK2,sK2)) | ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) | spl6_1),
% 1.63/0.59    inference(extensionality_resolution,[],[f50,f92])).
% 1.63/0.59  fof(f92,plain,(
% 1.63/0.59    k2_enumset1(sK2,sK2,sK2,sK2) != k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3) | spl6_1),
% 1.63/0.59    inference(avatar_component_clause,[],[f90])).
% 1.63/0.59  fof(f508,plain,(
% 1.63/0.59    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) | spl6_2),
% 1.63/0.59    inference(forward_demodulation,[],[f507,f420])).
% 1.63/0.59  fof(f507,plain,(
% 1.63/0.59    r1_tarski(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k1_xboole_0),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) | spl6_2),
% 1.63/0.59    inference(forward_demodulation,[],[f492,f316])).
% 1.63/0.59  fof(f492,plain,(
% 1.63/0.59    r1_tarski(k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(sK3,sK3)),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) | spl6_2),
% 1.63/0.59    inference(superposition,[],[f152,f172])).
% 1.63/0.59  fof(f172,plain,(
% 1.63/0.59    sK3 = k4_xboole_0(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) | spl6_2),
% 1.63/0.59    inference(resolution,[],[f78,f95])).
% 1.63/0.59  fof(f95,plain,(
% 1.63/0.59    ~r2_hidden(sK2,sK3) | spl6_2),
% 1.63/0.59    inference(avatar_component_clause,[],[f94])).
% 1.63/0.59  fof(f78,plain,(
% 1.63/0.59    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0) )),
% 1.63/0.59    inference(definition_unfolding,[],[f52,f73])).
% 1.63/0.59  fof(f52,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f26])).
% 1.63/0.59  fof(f152,plain,(
% 1.63/0.59    ( ! [X2,X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(X1,X2))) )),
% 1.63/0.59    inference(superposition,[],[f134,f77])).
% 1.63/0.59  fof(f98,plain,(
% 1.63/0.59    spl6_1 | ~spl6_2),
% 1.63/0.59    inference(avatar_split_clause,[],[f76,f94,f90])).
% 1.63/0.59  fof(f76,plain,(
% 1.63/0.59    ~r2_hidden(sK2,sK3) | k2_enumset1(sK2,sK2,sK2,sK2) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)),
% 1.63/0.59    inference(definition_unfolding,[],[f39,f73,f73])).
% 1.63/0.59  fof(f39,plain,(
% 1.63/0.59    ~r2_hidden(sK2,sK3) | k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3)),
% 1.63/0.59    inference(cnf_transformation,[],[f23])).
% 1.63/0.59  fof(f23,plain,(
% 1.63/0.59    (r2_hidden(sK2,sK3) | k1_tarski(sK2) != k4_xboole_0(k1_tarski(sK2),sK3)) & (~r2_hidden(sK2,sK3) | k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3))),
% 1.63/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f22])).
% 1.63/0.59  fof(f22,plain,(
% 1.63/0.59    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1))) => ((r2_hidden(sK2,sK3) | k1_tarski(sK2) != k4_xboole_0(k1_tarski(sK2),sK3)) & (~r2_hidden(sK2,sK3) | k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK3)))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f21,plain,(
% 1.63/0.59    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.63/0.59    inference(nnf_transformation,[],[f15])).
% 1.63/0.59  fof(f15,plain,(
% 1.63/0.59    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 1.63/0.59    inference(ennf_transformation,[],[f14])).
% 1.63/0.59  fof(f14,negated_conjecture,(
% 1.63/0.59    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.63/0.59    inference(negated_conjecture,[],[f13])).
% 1.63/0.59  fof(f13,conjecture,(
% 1.63/0.59    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 1.63/0.59  fof(f97,plain,(
% 1.63/0.59    ~spl6_1 | spl6_2),
% 1.63/0.59    inference(avatar_split_clause,[],[f75,f94,f90])).
% 1.63/0.59  fof(f75,plain,(
% 1.63/0.59    r2_hidden(sK2,sK3) | k2_enumset1(sK2,sK2,sK2,sK2) != k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK3)),
% 1.63/0.59    inference(definition_unfolding,[],[f40,f73,f73])).
% 1.63/0.59  fof(f40,plain,(
% 1.63/0.59    r2_hidden(sK2,sK3) | k1_tarski(sK2) != k4_xboole_0(k1_tarski(sK2),sK3)),
% 1.63/0.59    inference(cnf_transformation,[],[f23])).
% 1.63/0.59  % SZS output end Proof for theBenchmark
% 1.63/0.59  % (2481)------------------------------
% 1.63/0.59  % (2481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.59  % (2481)Termination reason: Refutation
% 1.63/0.59  
% 1.63/0.59  % (2481)Memory used [KB]: 11001
% 1.63/0.59  % (2481)Time elapsed: 0.176 s
% 1.63/0.59  % (2481)------------------------------
% 1.63/0.59  % (2481)------------------------------
% 1.63/0.59  % (2474)Success in time 0.211 s
%------------------------------------------------------------------------------
