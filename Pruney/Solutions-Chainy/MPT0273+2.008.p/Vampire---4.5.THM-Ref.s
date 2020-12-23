%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:19 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 432 expanded)
%              Number of leaves         :   27 ( 144 expanded)
%              Depth                    :   13
%              Number of atoms          :  517 (1576 expanded)
%              Number of equality atoms :  206 ( 878 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f741,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f124,f182,f187,f212,f214,f338,f356,f362,f391,f395,f417,f730,f734,f740])).

fof(f740,plain,
    ( ~ spl5_4
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f737])).

fof(f737,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f186,f105,f729,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f729,plain,
    ( r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f727])).

fof(f727,plain,
    ( spl5_11
  <=> r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f105,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f50,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f75,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f35,plain,(
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
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f186,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl5_4
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f734,plain,
    ( spl5_1
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f731])).

fof(f731,plain,
    ( $false
    | spl5_1
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f119,f107,f725,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f725,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f723])).

fof(f723,plain,
    ( spl5_10
  <=> r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f107,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f49,f78])).

fof(f49,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f119,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_1
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f730,plain,
    ( ~ spl5_10
    | spl5_11
    | spl5_9 ),
    inference(avatar_split_clause,[],[f718,f414,f727,f723])).

fof(f414,plain,
    ( spl5_9
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f718,plain,
    ( r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | ~ r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | spl5_9 ),
    inference(trivial_inequality_removal,[],[f683])).

fof(f683,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | ~ r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | spl5_9 ),
    inference(superposition,[],[f416,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f80,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f74,f78])).

fof(f74,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f72,f79])).

fof(f72,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f416,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f414])).

fof(f417,plain,
    ( spl5_1
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f396,f414,f184,f117])).

fof(f396,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))
    | ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f176,f229])).

fof(f229,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f215,f70])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f215,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f76,f71])).

fof(f71,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f76,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f176,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f82,f70])).

fof(f82,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f45,f80,f73,f79])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ( sK0 != sK1
        & ~ r2_hidden(sK1,sK2) )
      | r2_hidden(sK0,sK2)
      | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ( sK0 = sK1
          | r2_hidden(sK1,sK2) )
        & ~ r2_hidden(sK0,sK2) )
      | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ( ( X0 != X1
            & ~ r2_hidden(X1,X2) )
          | r2_hidden(X0,X2)
          | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ( X0 = X1
              | r2_hidden(X1,X2) )
            & ~ r2_hidden(X0,X2) )
          | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ( sK0 != sK1
          & ~ r2_hidden(sK1,sK2) )
        | r2_hidden(sK0,sK2)
        | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ( sK0 = sK1
            | r2_hidden(sK1,sK2) )
          & ~ r2_hidden(sK0,sK2) )
        | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2)
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2)
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_zfmisc_1)).

fof(f395,plain,
    ( spl5_1
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f392])).

fof(f392,plain,
    ( $false
    | spl5_1
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f119,f105,f390,f58])).

fof(f390,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f388])).

fof(f388,plain,
    ( spl5_8
  <=> r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f391,plain,
    ( ~ spl5_8
    | spl5_7 ),
    inference(avatar_split_clause,[],[f386,f359,f388])).

fof(f359,plain,
    ( spl5_7
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f386,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2))
    | spl5_7 ),
    inference(trivial_inequality_removal,[],[f366])).

fof(f366,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2))
    | spl5_7 ),
    inference(superposition,[],[f361,f114])).

fof(f114,plain,(
    ! [X2,X1] :
      ( k3_enumset1(X2,X2,X2,X2,X2) = k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X1)
      | ~ r2_hidden(X2,X1) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1)
      | X0 != X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f68,f80,f79])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | X0 != X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f361,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f359])).

fof(f362,plain,
    ( ~ spl5_7
    | spl5_6 ),
    inference(avatar_split_clause,[],[f357,f353,f359])).

fof(f353,plain,
    ( spl5_6
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f357,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2))
    | spl5_6 ),
    inference(superposition,[],[f355,f229])).

fof(f355,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f353])).

fof(f356,plain,
    ( ~ spl5_6
    | spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f341,f179,f121,f353])).

fof(f121,plain,
    ( spl5_2
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f179,plain,
    ( spl5_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f341,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f122,f180])).

fof(f180,plain,
    ( sK0 = sK1
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f179])).

fof(f122,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f338,plain,
    ( spl5_3
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | spl5_3
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f181,f181,f181,f211,f110])).

fof(f110,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f47,f78])).

fof(f47,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f211,plain,
    ( r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl5_5
  <=> r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f181,plain,
    ( sK0 != sK1
    | spl5_3 ),
    inference(avatar_component_clause,[],[f179])).

fof(f214,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f105,f118,f189])).

fof(f189,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X1,sK2) )
    | ~ spl5_2 ),
    inference(superposition,[],[f126,f123])).

fof(f123,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f126,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k5_xboole_0(X2,k3_xboole_0(X3,X2)))
      | ~ r2_hidden(X4,X3) ) ),
    inference(superposition,[],[f112,f70])).

fof(f112,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f61,f73])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
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
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
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
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f118,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f212,plain,
    ( spl5_4
    | spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f202,f121,f209,f184])).

fof(f202,plain,
    ( r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | r2_hidden(sK1,sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f201,f105])).

fof(f201,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
        | r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | r2_hidden(X1,sK2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f191,f162])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k3_xboole_0(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f59,f113])).

fof(f113,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f60,f73])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f191,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
        | r2_hidden(X3,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X3,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) )
    | ~ spl5_2 ),
    inference(superposition,[],[f58,f123])).

fof(f187,plain,
    ( spl5_4
    | spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f177,f121,f179,f184])).

fof(f177,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | sK0 = sK1
    | r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f83,f70])).

fof(f83,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f44,f80,f73,f79])).

fof(f44,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK2)
    | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f182,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f166,f121,f179,f117])).

fof(f166,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | sK0 != sK1
    | r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f81,f70])).

fof(f81,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f46,f80,f73,f79])).

fof(f46,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK2)
    | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f124,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f115,f121,f117])).

fof(f115,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f84,f70])).

fof(f84,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f43,f80,f73,f79])).

fof(f43,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:50:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.48  % (1137)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.48  % (1123)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  % (1122)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.50  % (1126)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.50  % (1118)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.51  % (1128)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.51  % (1127)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.51  % (1121)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.51  % (1134)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.51  % (1131)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.51  % (1139)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.52  % (1129)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.52  % (1133)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.52  % (1143)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.52  % (1146)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.52  % (1141)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.52  % (1144)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.52  % (1117)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.52  % (1132)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.52  % (1147)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.52  % (1145)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.52  % (1138)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.52  % (1135)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.53  % (1119)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.53  % (1120)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.53  % (1124)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.53  % (1142)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.53  % (1125)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.53  % (1130)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.54  % (1133)Refutation not found, incomplete strategy% (1133)------------------------------
% 0.19/0.54  % (1133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (1133)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (1133)Memory used [KB]: 10618
% 0.19/0.54  % (1133)Time elapsed: 0.139 s
% 0.19/0.54  % (1133)------------------------------
% 0.19/0.54  % (1133)------------------------------
% 0.19/0.54  % (1136)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.59  % (1141)Refutation found. Thanks to Tanya!
% 0.19/0.59  % SZS status Theorem for theBenchmark
% 0.19/0.59  % SZS output start Proof for theBenchmark
% 0.19/0.59  fof(f741,plain,(
% 0.19/0.59    $false),
% 0.19/0.59    inference(avatar_sat_refutation,[],[f124,f182,f187,f212,f214,f338,f356,f362,f391,f395,f417,f730,f734,f740])).
% 0.19/0.59  fof(f740,plain,(
% 0.19/0.59    ~spl5_4 | ~spl5_11),
% 0.19/0.59    inference(avatar_contradiction_clause,[],[f737])).
% 0.19/0.59  fof(f737,plain,(
% 0.19/0.59    $false | (~spl5_4 | ~spl5_11)),
% 0.19/0.59    inference(unit_resulting_resolution,[],[f186,f105,f729,f57])).
% 0.19/0.59  fof(f57,plain,(
% 0.19/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 0.19/0.59    inference(cnf_transformation,[],[f37])).
% 0.19/0.59  fof(f37,plain,(
% 0.19/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 0.19/0.59    inference(nnf_transformation,[],[f22])).
% 0.19/0.59  fof(f22,plain,(
% 0.19/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.19/0.59    inference(ennf_transformation,[],[f4])).
% 0.19/0.59  fof(f4,axiom,(
% 0.19/0.59    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.19/0.59  fof(f729,plain,(
% 0.19/0.59    r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | ~spl5_11),
% 0.19/0.59    inference(avatar_component_clause,[],[f727])).
% 0.19/0.59  fof(f727,plain,(
% 0.19/0.59    spl5_11 <=> r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.19/0.59  fof(f105,plain,(
% 0.19/0.59    ( ! [X0,X5,X1] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5))) )),
% 0.19/0.59    inference(equality_resolution,[],[f104])).
% 0.19/0.59  fof(f104,plain,(
% 0.19/0.59    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X5) != X3) )),
% 0.19/0.59    inference(equality_resolution,[],[f89])).
% 0.19/0.59  fof(f89,plain,(
% 0.19/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.19/0.59    inference(definition_unfolding,[],[f50,f78])).
% 0.19/0.59  fof(f78,plain,(
% 0.19/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.19/0.59    inference(definition_unfolding,[],[f75,f77])).
% 0.19/0.59  fof(f77,plain,(
% 0.19/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.19/0.59    inference(cnf_transformation,[],[f11])).
% 0.19/0.59  fof(f11,axiom,(
% 0.19/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.59  fof(f75,plain,(
% 0.19/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.19/0.59    inference(cnf_transformation,[],[f10])).
% 0.19/0.59  fof(f10,axiom,(
% 0.19/0.59    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.59  fof(f50,plain,(
% 0.19/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.19/0.59    inference(cnf_transformation,[],[f36])).
% 0.19/0.59  fof(f36,plain,(
% 0.19/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.19/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 0.19/0.59  fof(f35,plain,(
% 0.19/0.59    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 0.19/0.59    introduced(choice_axiom,[])).
% 0.19/0.59  fof(f34,plain,(
% 0.19/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.19/0.59    inference(rectify,[],[f33])).
% 0.19/0.59  fof(f33,plain,(
% 0.19/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.19/0.59    inference(flattening,[],[f32])).
% 0.19/0.59  fof(f32,plain,(
% 0.19/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.19/0.59    inference(nnf_transformation,[],[f20])).
% 0.19/0.59  fof(f20,plain,(
% 0.19/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.19/0.59    inference(ennf_transformation,[],[f7])).
% 0.19/0.59  fof(f7,axiom,(
% 0.19/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.19/0.59  fof(f186,plain,(
% 0.19/0.59    r2_hidden(sK1,sK2) | ~spl5_4),
% 0.19/0.59    inference(avatar_component_clause,[],[f184])).
% 0.19/0.59  fof(f184,plain,(
% 0.19/0.59    spl5_4 <=> r2_hidden(sK1,sK2)),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.59  fof(f734,plain,(
% 0.19/0.59    spl5_1 | spl5_10),
% 0.19/0.59    inference(avatar_contradiction_clause,[],[f731])).
% 0.19/0.59  fof(f731,plain,(
% 0.19/0.59    $false | (spl5_1 | spl5_10)),
% 0.19/0.59    inference(unit_resulting_resolution,[],[f119,f107,f725,f58])).
% 0.19/0.59  fof(f58,plain,(
% 0.19/0.59    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.19/0.59    inference(cnf_transformation,[],[f37])).
% 0.19/0.59  fof(f725,plain,(
% 0.19/0.59    ~r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | spl5_10),
% 0.19/0.59    inference(avatar_component_clause,[],[f723])).
% 0.19/0.59  fof(f723,plain,(
% 0.19/0.59    spl5_10 <=> r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.19/0.59  fof(f107,plain,(
% 0.19/0.59    ( ! [X2,X0,X5] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X5,X2))) )),
% 0.19/0.59    inference(equality_resolution,[],[f106])).
% 0.19/0.59  fof(f106,plain,(
% 0.19/0.59    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X5,X2) != X3) )),
% 0.19/0.59    inference(equality_resolution,[],[f90])).
% 0.19/0.59  fof(f90,plain,(
% 0.19/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.19/0.59    inference(definition_unfolding,[],[f49,f78])).
% 0.19/0.59  fof(f49,plain,(
% 0.19/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.19/0.59    inference(cnf_transformation,[],[f36])).
% 0.19/0.59  fof(f119,plain,(
% 0.19/0.59    ~r2_hidden(sK0,sK2) | spl5_1),
% 0.19/0.59    inference(avatar_component_clause,[],[f117])).
% 0.19/0.59  fof(f117,plain,(
% 0.19/0.59    spl5_1 <=> r2_hidden(sK0,sK2)),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.59  fof(f730,plain,(
% 0.19/0.59    ~spl5_10 | spl5_11 | spl5_9),
% 0.19/0.59    inference(avatar_split_clause,[],[f718,f414,f727,f723])).
% 0.19/0.59  fof(f414,plain,(
% 0.19/0.59    spl5_9 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.19/0.59  fof(f718,plain,(
% 0.19/0.59    r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | ~r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | spl5_9),
% 0.19/0.59    inference(trivial_inequality_removal,[],[f683])).
% 0.19/0.59  fof(f683,plain,(
% 0.19/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | r2_hidden(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | ~r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | spl5_9),
% 0.19/0.59    inference(superposition,[],[f416,f102])).
% 0.19/0.59  fof(f102,plain,(
% 0.19/0.59    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.59    inference(definition_unfolding,[],[f67,f80,f79])).
% 0.19/0.59  fof(f79,plain,(
% 0.19/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.19/0.59    inference(definition_unfolding,[],[f74,f78])).
% 0.19/0.59  fof(f74,plain,(
% 0.19/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.59    inference(cnf_transformation,[],[f9])).
% 0.19/0.59  fof(f9,axiom,(
% 0.19/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.59  fof(f80,plain,(
% 0.19/0.59    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.19/0.59    inference(definition_unfolding,[],[f72,f79])).
% 0.19/0.59  fof(f72,plain,(
% 0.19/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.59    inference(cnf_transformation,[],[f8])).
% 0.19/0.59  fof(f8,axiom,(
% 0.19/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.59  fof(f67,plain,(
% 0.19/0.59    ( ! [X2,X0,X1] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.59    inference(cnf_transformation,[],[f26])).
% 0.19/0.59  fof(f26,plain,(
% 0.19/0.59    ! [X0,X1,X2] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.19/0.59    inference(flattening,[],[f25])).
% 0.19/0.59  fof(f25,plain,(
% 0.19/0.59    ! [X0,X1,X2] : ((k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))) | ~r2_hidden(X0,X1))),
% 0.19/0.59    inference(ennf_transformation,[],[f14])).
% 0.19/0.59  fof(f14,axiom,(
% 0.19/0.59    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 0.19/0.59  fof(f416,plain,(
% 0.19/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | spl5_9),
% 0.19/0.59    inference(avatar_component_clause,[],[f414])).
% 0.19/0.59  fof(f417,plain,(
% 0.19/0.59    spl5_1 | ~spl5_4 | ~spl5_9),
% 0.19/0.59    inference(avatar_split_clause,[],[f396,f414,f184,f117])).
% 0.19/0.59  fof(f396,plain,(
% 0.19/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) | ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2)),
% 0.19/0.59    inference(forward_demodulation,[],[f176,f229])).
% 0.19/0.59  fof(f229,plain,(
% 0.19/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.19/0.59    inference(forward_demodulation,[],[f215,f70])).
% 0.19/0.59  fof(f70,plain,(
% 0.19/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.59    inference(cnf_transformation,[],[f1])).
% 0.19/0.59  fof(f1,axiom,(
% 0.19/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.59  fof(f215,plain,(
% 0.19/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0)) )),
% 0.19/0.59    inference(superposition,[],[f76,f71])).
% 0.19/0.59  fof(f71,plain,(
% 0.19/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.19/0.59    inference(cnf_transformation,[],[f18])).
% 0.19/0.59  fof(f18,plain,(
% 0.19/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.19/0.59    inference(rectify,[],[f3])).
% 0.19/0.59  fof(f3,axiom,(
% 0.19/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.19/0.59  fof(f76,plain,(
% 0.19/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 0.19/0.59    inference(cnf_transformation,[],[f6])).
% 0.19/0.59  fof(f6,axiom,(
% 0.19/0.59    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 0.19/0.59  fof(f176,plain,(
% 0.19/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2)),
% 0.19/0.59    inference(forward_demodulation,[],[f82,f70])).
% 0.19/0.59  fof(f82,plain,(
% 0.19/0.59    ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 0.19/0.59    inference(definition_unfolding,[],[f45,f80,f73,f79])).
% 0.19/0.59  fof(f73,plain,(
% 0.19/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.59    inference(cnf_transformation,[],[f5])).
% 0.19/0.59  fof(f5,axiom,(
% 0.19/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.19/0.59  fof(f45,plain,(
% 0.19/0.59    ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.19/0.59    inference(cnf_transformation,[],[f31])).
% 0.19/0.59  fof(f31,plain,(
% 0.19/0.59    ((sK0 != sK1 & ~r2_hidden(sK1,sK2)) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & (((sK0 = sK1 | r2_hidden(sK1,sK2)) & ~r2_hidden(sK0,sK2)) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 0.19/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f30])).
% 0.19/0.59  fof(f30,plain,(
% 0.19/0.59    ? [X0,X1,X2] : (((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2))) => (((sK0 != sK1 & ~r2_hidden(sK1,sK2)) | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & (((sK0 = sK1 | r2_hidden(sK1,sK2)) & ~r2_hidden(sK0,sK2)) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 0.19/0.59    introduced(choice_axiom,[])).
% 0.19/0.59  fof(f29,plain,(
% 0.19/0.59    ? [X0,X1,X2] : (((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.19/0.59    inference(flattening,[],[f28])).
% 0.19/0.59  fof(f28,plain,(
% 0.19/0.59    ? [X0,X1,X2] : ((((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.19/0.59    inference(nnf_transformation,[],[f19])).
% 0.19/0.59  fof(f19,plain,(
% 0.19/0.59    ? [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 0.19/0.59    inference(ennf_transformation,[],[f17])).
% 0.19/0.59  fof(f17,negated_conjecture,(
% 0.19/0.59    ~! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 0.19/0.59    inference(negated_conjecture,[],[f16])).
% 0.19/0.59  fof(f16,conjecture,(
% 0.19/0.59    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_zfmisc_1)).
% 0.19/0.59  fof(f395,plain,(
% 0.19/0.59    spl5_1 | spl5_8),
% 0.19/0.59    inference(avatar_contradiction_clause,[],[f392])).
% 0.19/0.59  fof(f392,plain,(
% 0.19/0.59    $false | (spl5_1 | spl5_8)),
% 0.19/0.59    inference(unit_resulting_resolution,[],[f119,f105,f390,f58])).
% 0.19/0.59  fof(f390,plain,(
% 0.19/0.59    ~r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)) | spl5_8),
% 0.19/0.59    inference(avatar_component_clause,[],[f388])).
% 0.19/0.59  fof(f388,plain,(
% 0.19/0.59    spl5_8 <=> r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2))),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.19/0.59  fof(f391,plain,(
% 0.19/0.59    ~spl5_8 | spl5_7),
% 0.19/0.59    inference(avatar_split_clause,[],[f386,f359,f388])).
% 0.19/0.59  fof(f359,plain,(
% 0.19/0.59    spl5_7 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2))),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.19/0.59  fof(f386,plain,(
% 0.19/0.59    ~r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)) | spl5_7),
% 0.19/0.59    inference(trivial_inequality_removal,[],[f366])).
% 0.19/0.59  fof(f366,plain,(
% 0.19/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)) | spl5_7),
% 0.19/0.59    inference(superposition,[],[f361,f114])).
% 0.19/0.59  fof(f114,plain,(
% 0.19/0.59    ( ! [X2,X1] : (k3_enumset1(X2,X2,X2,X2,X2) = k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),X1) | ~r2_hidden(X2,X1)) )),
% 0.19/0.59    inference(equality_resolution,[],[f101])).
% 0.19/0.59  fof(f101,plain,(
% 0.19/0.59    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X2),X1) | X0 != X2 | ~r2_hidden(X0,X1)) )),
% 0.19/0.59    inference(definition_unfolding,[],[f68,f80,f79])).
% 0.19/0.59  fof(f68,plain,(
% 0.19/0.59    ( ! [X2,X0,X1] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | X0 != X2 | ~r2_hidden(X0,X1)) )),
% 0.19/0.59    inference(cnf_transformation,[],[f26])).
% 0.19/0.59  fof(f361,plain,(
% 0.19/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)) | spl5_7),
% 0.19/0.59    inference(avatar_component_clause,[],[f359])).
% 0.19/0.59  fof(f362,plain,(
% 0.19/0.59    ~spl5_7 | spl5_6),
% 0.19/0.59    inference(avatar_split_clause,[],[f357,f353,f359])).
% 0.19/0.59  fof(f353,plain,(
% 0.19/0.59    spl5_6 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.19/0.59  fof(f357,plain,(
% 0.19/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK2)) | spl5_6),
% 0.19/0.59    inference(superposition,[],[f355,f229])).
% 0.19/0.59  fof(f355,plain,(
% 0.19/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | spl5_6),
% 0.19/0.59    inference(avatar_component_clause,[],[f353])).
% 0.19/0.59  fof(f356,plain,(
% 0.19/0.59    ~spl5_6 | spl5_2 | ~spl5_3),
% 0.19/0.59    inference(avatar_split_clause,[],[f341,f179,f121,f353])).
% 0.19/0.59  fof(f121,plain,(
% 0.19/0.59    spl5_2 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.59  fof(f179,plain,(
% 0.19/0.59    spl5_3 <=> sK0 = sK1),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.59  fof(f341,plain,(
% 0.19/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | (spl5_2 | ~spl5_3)),
% 0.19/0.59    inference(forward_demodulation,[],[f122,f180])).
% 0.19/0.59  fof(f180,plain,(
% 0.19/0.59    sK0 = sK1 | ~spl5_3),
% 0.19/0.59    inference(avatar_component_clause,[],[f179])).
% 0.19/0.59  fof(f122,plain,(
% 0.19/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | spl5_2),
% 0.19/0.59    inference(avatar_component_clause,[],[f121])).
% 0.19/0.59  fof(f338,plain,(
% 0.19/0.59    spl5_3 | ~spl5_5),
% 0.19/0.59    inference(avatar_contradiction_clause,[],[f332])).
% 0.19/0.59  fof(f332,plain,(
% 0.19/0.59    $false | (spl5_3 | ~spl5_5)),
% 0.19/0.59    inference(unit_resulting_resolution,[],[f181,f181,f181,f211,f110])).
% 0.19/0.59  fof(f110,plain,(
% 0.19/0.59    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 0.19/0.59    inference(equality_resolution,[],[f92])).
% 0.19/0.59  fof(f92,plain,(
% 0.19/0.59    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.19/0.59    inference(definition_unfolding,[],[f47,f78])).
% 0.19/0.59  fof(f47,plain,(
% 0.19/0.59    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.19/0.59    inference(cnf_transformation,[],[f36])).
% 0.19/0.59  fof(f211,plain,(
% 0.19/0.59    r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~spl5_5),
% 0.19/0.59    inference(avatar_component_clause,[],[f209])).
% 0.19/0.59  fof(f209,plain,(
% 0.19/0.59    spl5_5 <=> r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.19/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.19/0.59  fof(f181,plain,(
% 0.19/0.59    sK0 != sK1 | spl5_3),
% 0.19/0.59    inference(avatar_component_clause,[],[f179])).
% 0.19/0.59  fof(f214,plain,(
% 0.19/0.59    ~spl5_1 | ~spl5_2),
% 0.19/0.59    inference(avatar_contradiction_clause,[],[f213])).
% 0.19/0.59  fof(f213,plain,(
% 0.19/0.59    $false | (~spl5_1 | ~spl5_2)),
% 0.19/0.59    inference(unit_resulting_resolution,[],[f105,f118,f189])).
% 0.19/0.59  fof(f189,plain,(
% 0.19/0.59    ( ! [X1] : (~r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X1,sK2)) ) | ~spl5_2),
% 0.19/0.59    inference(superposition,[],[f126,f123])).
% 0.19/0.59  fof(f123,plain,(
% 0.19/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~spl5_2),
% 0.19/0.59    inference(avatar_component_clause,[],[f121])).
% 0.19/0.59  fof(f126,plain,(
% 0.19/0.59    ( ! [X4,X2,X3] : (~r2_hidden(X4,k5_xboole_0(X2,k3_xboole_0(X3,X2))) | ~r2_hidden(X4,X3)) )),
% 0.19/0.59    inference(superposition,[],[f112,f70])).
% 0.19/0.59  fof(f112,plain,(
% 0.19/0.59    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 0.19/0.59    inference(equality_resolution,[],[f98])).
% 0.19/0.59  fof(f98,plain,(
% 0.19/0.59    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.19/0.59    inference(definition_unfolding,[],[f61,f73])).
% 0.19/0.59  fof(f61,plain,(
% 0.19/0.59    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.19/0.59    inference(cnf_transformation,[],[f42])).
% 0.19/0.59  fof(f42,plain,(
% 0.19/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.19/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 0.19/0.59  fof(f41,plain,(
% 0.19/0.59    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.19/0.59    introduced(choice_axiom,[])).
% 0.19/0.59  fof(f40,plain,(
% 0.19/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.19/0.59    inference(rectify,[],[f39])).
% 0.19/0.59  fof(f39,plain,(
% 0.19/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.19/0.59    inference(flattening,[],[f38])).
% 0.19/0.59  fof(f38,plain,(
% 0.19/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.19/0.59    inference(nnf_transformation,[],[f2])).
% 0.19/0.59  fof(f2,axiom,(
% 0.19/0.59    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.19/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.19/0.59  fof(f118,plain,(
% 0.19/0.59    r2_hidden(sK0,sK2) | ~spl5_1),
% 0.19/0.59    inference(avatar_component_clause,[],[f117])).
% 0.19/0.59  fof(f212,plain,(
% 0.19/0.59    spl5_4 | spl5_5 | ~spl5_2),
% 0.19/0.59    inference(avatar_split_clause,[],[f202,f121,f209,f184])).
% 0.19/0.59  fof(f202,plain,(
% 0.19/0.59    r2_hidden(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK1,sK2) | ~spl5_2),
% 0.19/0.59    inference(resolution,[],[f201,f105])).
% 0.19/0.59  fof(f201,plain,(
% 0.19/0.59    ( ! [X1] : (~r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(X1,sK2)) ) | ~spl5_2),
% 0.19/0.59    inference(resolution,[],[f191,f162])).
% 0.19/0.59  fof(f162,plain,(
% 0.19/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,X2)) | r2_hidden(X0,X1)) )),
% 0.19/0.59    inference(duplicate_literal_removal,[],[f149])).
% 0.19/0.59  fof(f149,plain,(
% 0.19/0.59    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k3_xboole_0(X1,X2)) | r2_hidden(X0,X1)) )),
% 0.19/0.59    inference(resolution,[],[f59,f113])).
% 0.19/0.59  fof(f113,plain,(
% 0.19/0.59    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 0.19/0.59    inference(equality_resolution,[],[f99])).
% 0.19/0.59  fof(f99,plain,(
% 0.19/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.19/0.59    inference(definition_unfolding,[],[f60,f73])).
% 0.19/0.59  fof(f60,plain,(
% 0.19/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.19/0.59    inference(cnf_transformation,[],[f42])).
% 0.19/0.59  fof(f59,plain,(
% 0.19/0.59    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 0.19/0.59    inference(cnf_transformation,[],[f37])).
% 0.19/0.59  fof(f191,plain,(
% 0.19/0.59    ( ! [X3] : (r2_hidden(X3,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | r2_hidden(X3,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X3,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ) | ~spl5_2),
% 0.19/0.59    inference(superposition,[],[f58,f123])).
% 0.19/0.59  fof(f187,plain,(
% 0.19/0.59    spl5_4 | spl5_3 | spl5_2),
% 0.19/0.59    inference(avatar_split_clause,[],[f177,f121,f179,f184])).
% 0.19/0.59  fof(f177,plain,(
% 0.19/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | sK0 = sK1 | r2_hidden(sK1,sK2)),
% 0.19/0.59    inference(forward_demodulation,[],[f83,f70])).
% 0.19/0.59  fof(f83,plain,(
% 0.19/0.59    sK0 = sK1 | r2_hidden(sK1,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 0.19/0.59    inference(definition_unfolding,[],[f44,f80,f73,f79])).
% 0.19/0.59  fof(f44,plain,(
% 0.19/0.59    sK0 = sK1 | r2_hidden(sK1,sK2) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.19/0.59    inference(cnf_transformation,[],[f31])).
% 0.19/0.59  fof(f182,plain,(
% 0.19/0.59    spl5_1 | ~spl5_3 | ~spl5_2),
% 0.19/0.59    inference(avatar_split_clause,[],[f166,f121,f179,f117])).
% 0.19/0.59  fof(f166,plain,(
% 0.19/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | sK0 != sK1 | r2_hidden(sK0,sK2)),
% 0.19/0.59    inference(forward_demodulation,[],[f81,f70])).
% 0.19/0.59  fof(f81,plain,(
% 0.19/0.59    sK0 != sK1 | r2_hidden(sK0,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 0.19/0.59    inference(definition_unfolding,[],[f46,f80,f73,f79])).
% 0.19/0.59  fof(f46,plain,(
% 0.19/0.59    sK0 != sK1 | r2_hidden(sK0,sK2) | k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.19/0.59    inference(cnf_transformation,[],[f31])).
% 0.19/0.59  fof(f124,plain,(
% 0.19/0.59    ~spl5_1 | spl5_2),
% 0.19/0.59    inference(avatar_split_clause,[],[f115,f121,f117])).
% 0.19/0.59  fof(f115,plain,(
% 0.19/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK0,sK2)),
% 0.19/0.59    inference(forward_demodulation,[],[f84,f70])).
% 0.19/0.59  fof(f84,plain,(
% 0.19/0.59    ~r2_hidden(sK0,sK2) | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),
% 0.19/0.59    inference(definition_unfolding,[],[f43,f80,f73,f79])).
% 0.19/0.59  fof(f43,plain,(
% 0.19/0.59    ~r2_hidden(sK0,sK2) | k1_tarski(sK0) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.19/0.59    inference(cnf_transformation,[],[f31])).
% 0.19/0.59  % SZS output end Proof for theBenchmark
% 0.19/0.59  % (1141)------------------------------
% 0.19/0.59  % (1141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.59  % (1141)Termination reason: Refutation
% 0.19/0.59  
% 0.19/0.59  % (1141)Memory used [KB]: 11513
% 0.19/0.59  % (1141)Time elapsed: 0.137 s
% 0.19/0.59  % (1141)------------------------------
% 0.19/0.59  % (1141)------------------------------
% 1.86/0.61  % (1116)Success in time 0.257 s
%------------------------------------------------------------------------------
