%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:06 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 493 expanded)
%              Number of leaves         :   22 ( 162 expanded)
%              Depth                    :   18
%              Number of atoms          :  456 (1344 expanded)
%              Number of equality atoms :  197 ( 849 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f788,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f126,f127,f194,f290,f657,f682,f768])).

fof(f768,plain,
    ( spl6_1
    | ~ spl6_3
    | ~ spl6_26 ),
    inference(avatar_contradiction_clause,[],[f728])).

fof(f728,plain,
    ( $false
    | spl6_1
    | ~ spl6_3
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f292,f642])).

fof(f642,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f641])).

fof(f641,plain,
    ( spl6_26
  <=> k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f292,plain,
    ( k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl6_1
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f115,f180])).

fof(f180,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f115,plain,
    ( sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl6_1
  <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f682,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | spl6_29 ),
    inference(avatar_contradiction_clause,[],[f678])).

fof(f678,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | spl6_29 ),
    inference(subsumption_resolution,[],[f656,f326])).

fof(f326,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f318,f102])).

fof(f102,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f53,f76])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f318,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(duplicate_literal_removal,[],[f313])).

fof(f313,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f224,f270])).

fof(f270,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | r2_hidden(X0,k1_xboole_0)
        | r2_hidden(X0,sK2) )
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f128,f180])).

fof(f128,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | r2_hidden(X0,sK1)
      | r2_hidden(X0,sK2) ) ),
    inference(superposition,[],[f108,f80])).

fof(f80,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f40,f76,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f74])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f40,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f21])).

fof(f21,plain,
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

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f108,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f61,f75])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f656,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | spl6_29 ),
    inference(avatar_component_clause,[],[f655])).

fof(f655,plain,
    ( spl6_29
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f657,plain,
    ( spl6_26
    | ~ spl6_29
    | spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f653,f121,f114,f655,f641])).

fof(f653,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl6_1
    | ~ spl6_3 ),
    inference(trivial_inequality_removal,[],[f652])).

fof(f652,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | sK0 != sK0
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl6_1
    | ~ spl6_3 ),
    inference(superposition,[],[f82,f602])).

fof(f602,plain,
    ( sK0 = sK4(sK0,k1_xboole_0)
    | spl6_1
    | ~ spl6_3 ),
    inference(trivial_inequality_removal,[],[f601])).

fof(f601,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 = sK4(sK0,k1_xboole_0)
    | spl6_1
    | ~ spl6_3 ),
    inference(duplicate_literal_removal,[],[f571])).

fof(f571,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 = sK4(sK0,k1_xboole_0)
    | sK0 = sK4(sK0,k1_xboole_0)
    | spl6_1
    | ~ spl6_3 ),
    inference(superposition,[],[f292,f246])).

fof(f246,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k3_enumset1(X3,X3,X3,X3,X3)
        | sK4(X3,k1_xboole_0) = X3
        | sK0 = sK4(X3,k1_xboole_0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f227,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | sK4(X0,X1) = X0
      | k3_enumset1(X0,X0,X0,X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f54,f76])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK4(X0,X1) = X0
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | sK0 = X0 )
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f132,f180])).

fof(f132,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK0 = X0 ) ),
    inference(resolution,[],[f129,f103])).

fof(f103,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f52,f76])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f129,plain,(
    ! [X1] :
      ( r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(superposition,[],[f107,f80])).

fof(f107,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f62,f75])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | sK4(X0,X1) != X0
      | k3_enumset1(X0,X0,X0,X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f55,f76])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK4(X0,X1) != X0
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f290,plain,
    ( spl6_4
    | spl6_2 ),
    inference(avatar_split_clause,[],[f285,f117,f124])).

fof(f124,plain,
    ( spl6_4
  <=> sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f285,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f222,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f56,f76,f76])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f222,plain,(
    r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,
    ( r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f144,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f144,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2)
      | r1_tarski(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ) ),
    inference(resolution,[],[f130,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f130,plain,(
    ! [X2] :
      ( r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X2,sK2) ) ),
    inference(superposition,[],[f106,f80])).

fof(f106,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f63,f75])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f194,plain,
    ( spl6_3
    | spl6_1 ),
    inference(avatar_split_clause,[],[f193,f114,f121])).

fof(f193,plain,
    ( sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f189])).

fof(f189,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f151,f88])).

fof(f151,plain,(
    ! [X1] : r1_tarski(sK1,k3_enumset1(X1,X1,X1,X1,sK0)) ),
    inference(resolution,[],[f131,f110])).

fof(f110,plain,(
    ! [X2,X1] : r1_tarski(k3_enumset1(X2,X2,X2,X2,X2),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2))
      | k3_enumset1(X2,X2,X2,X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f70,f74,f76])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f131,plain,(
    ! [X3] :
      ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X3)
      | r1_tarski(sK1,X3) ) ),
    inference(superposition,[],[f89,f80])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f60,f75])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f127,plain,
    ( ~ spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f79,f124,f114])).

fof(f79,plain,
    ( sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f41,f76,f76])).

fof(f41,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f126,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f78,f124,f121])).

fof(f78,plain,
    ( sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f42,f76])).

fof(f42,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f119,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f77,f117,f114])).

fof(f77,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f43,f76])).

fof(f43,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:19:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (6878)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.56  % (6904)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.57  % (6888)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.57  % (6884)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.58  % (6883)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.35/0.58  % (6877)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.35/0.58  % (6881)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.35/0.58  % (6876)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.75/0.59  % (6880)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.75/0.59  % (6875)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.75/0.59  % (6879)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.75/0.59  % (6898)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.75/0.60  % (6896)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.75/0.60  % (6887)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.75/0.60  % (6886)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.75/0.60  % (6890)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.75/0.60  % (6893)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.75/0.61  % (6901)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.75/0.61  % (6903)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.75/0.61  % (6892)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.75/0.61  % (6902)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.75/0.61  % (6895)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.75/0.61  % (6897)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.75/0.61  % (6894)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.75/0.61  % (6882)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.75/0.61  % (6892)Refutation not found, incomplete strategy% (6892)------------------------------
% 1.75/0.61  % (6892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.62  % (6885)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.75/0.62  % (6889)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.75/0.62  % (6892)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.62  
% 1.75/0.62  % (6892)Memory used [KB]: 10618
% 1.75/0.62  % (6892)Time elapsed: 0.178 s
% 1.75/0.62  % (6892)------------------------------
% 1.75/0.62  % (6892)------------------------------
% 1.75/0.62  % (6891)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.75/0.62  % (6899)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.75/0.63  % (6877)Refutation found. Thanks to Tanya!
% 1.75/0.63  % SZS status Theorem for theBenchmark
% 1.75/0.63  % SZS output start Proof for theBenchmark
% 1.75/0.63  fof(f788,plain,(
% 1.75/0.63    $false),
% 1.75/0.63    inference(avatar_sat_refutation,[],[f119,f126,f127,f194,f290,f657,f682,f768])).
% 1.75/0.63  fof(f768,plain,(
% 1.75/0.63    spl6_1 | ~spl6_3 | ~spl6_26),
% 1.75/0.63    inference(avatar_contradiction_clause,[],[f728])).
% 1.75/0.63  fof(f728,plain,(
% 1.75/0.63    $false | (spl6_1 | ~spl6_3 | ~spl6_26)),
% 1.75/0.63    inference(subsumption_resolution,[],[f292,f642])).
% 1.75/0.63  fof(f642,plain,(
% 1.75/0.63    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl6_26),
% 1.75/0.63    inference(avatar_component_clause,[],[f641])).
% 1.75/0.63  fof(f641,plain,(
% 1.75/0.63    spl6_26 <=> k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.75/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.75/0.63  fof(f292,plain,(
% 1.75/0.63    k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | (spl6_1 | ~spl6_3)),
% 1.75/0.63    inference(forward_demodulation,[],[f115,f180])).
% 1.75/0.63  fof(f180,plain,(
% 1.75/0.63    k1_xboole_0 = sK1 | ~spl6_3),
% 1.75/0.63    inference(avatar_component_clause,[],[f121])).
% 1.75/0.63  fof(f121,plain,(
% 1.75/0.63    spl6_3 <=> k1_xboole_0 = sK1),
% 1.75/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.75/0.63  fof(f115,plain,(
% 1.75/0.63    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | spl6_1),
% 1.75/0.63    inference(avatar_component_clause,[],[f114])).
% 1.75/0.63  fof(f114,plain,(
% 1.75/0.63    spl6_1 <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.75/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.75/0.63  fof(f682,plain,(
% 1.75/0.63    ~spl6_2 | ~spl6_3 | spl6_29),
% 1.75/0.63    inference(avatar_contradiction_clause,[],[f678])).
% 1.75/0.63  fof(f678,plain,(
% 1.75/0.63    $false | (~spl6_2 | ~spl6_3 | spl6_29)),
% 1.75/0.63    inference(subsumption_resolution,[],[f656,f326])).
% 1.75/0.63  fof(f326,plain,(
% 1.75/0.63    r2_hidden(sK0,k1_xboole_0) | (~spl6_2 | ~spl6_3)),
% 1.75/0.63    inference(resolution,[],[f318,f102])).
% 1.75/0.63  fof(f102,plain,(
% 1.75/0.63    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 1.75/0.63    inference(equality_resolution,[],[f101])).
% 1.75/0.63  fof(f101,plain,(
% 1.75/0.63    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 1.75/0.63    inference(equality_resolution,[],[f84])).
% 1.75/0.63  fof(f84,plain,(
% 1.75/0.63    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.75/0.63    inference(definition_unfolding,[],[f53,f76])).
% 1.75/0.63  fof(f76,plain,(
% 1.75/0.63    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.75/0.63    inference(definition_unfolding,[],[f45,f74])).
% 1.75/0.63  fof(f74,plain,(
% 1.75/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.75/0.63    inference(definition_unfolding,[],[f47,f73])).
% 1.75/0.63  fof(f73,plain,(
% 1.75/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.75/0.63    inference(definition_unfolding,[],[f59,f72])).
% 1.75/0.63  fof(f72,plain,(
% 1.75/0.63    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.75/0.63    inference(cnf_transformation,[],[f10])).
% 1.75/0.63  fof(f10,axiom,(
% 1.75/0.63    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.75/0.63  fof(f59,plain,(
% 1.75/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.75/0.63    inference(cnf_transformation,[],[f9])).
% 1.75/0.63  fof(f9,axiom,(
% 1.75/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.75/0.63  fof(f47,plain,(
% 1.75/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.75/0.63    inference(cnf_transformation,[],[f8])).
% 1.75/0.63  fof(f8,axiom,(
% 1.75/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.75/0.63  fof(f45,plain,(
% 1.75/0.63    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.75/0.63    inference(cnf_transformation,[],[f7])).
% 1.75/0.63  fof(f7,axiom,(
% 1.75/0.63    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.75/0.63  fof(f53,plain,(
% 1.75/0.63    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.75/0.63    inference(cnf_transformation,[],[f30])).
% 1.75/0.63  fof(f30,plain,(
% 1.75/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.75/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 1.75/0.63  fof(f29,plain,(
% 1.75/0.63    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.75/0.63    introduced(choice_axiom,[])).
% 1.75/0.63  fof(f28,plain,(
% 1.75/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.75/0.63    inference(rectify,[],[f27])).
% 1.75/0.63  fof(f27,plain,(
% 1.75/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.75/0.63    inference(nnf_transformation,[],[f6])).
% 1.75/0.63  fof(f6,axiom,(
% 1.75/0.63    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.75/0.63  fof(f318,plain,(
% 1.75/0.63    ( ! [X0] : (~r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(X0,k1_xboole_0)) ) | (~spl6_2 | ~spl6_3)),
% 1.75/0.63    inference(duplicate_literal_removal,[],[f313])).
% 1.75/0.63  fof(f313,plain,(
% 1.75/0.63    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(X0,k1_xboole_0)) ) | (~spl6_2 | ~spl6_3)),
% 1.75/0.63    inference(backward_demodulation,[],[f224,f270])).
% 1.75/0.63  fof(f270,plain,(
% 1.75/0.63    k1_xboole_0 = sK2 | ~spl6_2),
% 1.75/0.63    inference(avatar_component_clause,[],[f117])).
% 1.75/0.63  fof(f117,plain,(
% 1.75/0.63    spl6_2 <=> k1_xboole_0 = sK2),
% 1.75/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.75/0.63  fof(f224,plain,(
% 1.75/0.63    ( ! [X0] : (~r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,sK2)) ) | ~spl6_3),
% 1.75/0.63    inference(backward_demodulation,[],[f128,f180])).
% 1.75/0.63  fof(f128,plain,(
% 1.75/0.63    ( ! [X0] : (~r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r2_hidden(X0,sK1) | r2_hidden(X0,sK2)) )),
% 1.75/0.63    inference(superposition,[],[f108,f80])).
% 1.75/0.63  fof(f80,plain,(
% 1.75/0.63    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.75/0.63    inference(definition_unfolding,[],[f40,f76,f75])).
% 1.75/0.63  fof(f75,plain,(
% 1.75/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.75/0.63    inference(definition_unfolding,[],[f46,f74])).
% 1.75/0.63  fof(f46,plain,(
% 1.75/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.75/0.63    inference(cnf_transformation,[],[f13])).
% 1.75/0.63  fof(f13,axiom,(
% 1.75/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.75/0.63  fof(f40,plain,(
% 1.75/0.63    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.75/0.63    inference(cnf_transformation,[],[f22])).
% 1.75/0.63  fof(f22,plain,(
% 1.75/0.63    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.75/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f21])).
% 1.75/0.63  fof(f21,plain,(
% 1.75/0.63    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.75/0.63    introduced(choice_axiom,[])).
% 1.75/0.63  fof(f16,plain,(
% 1.75/0.63    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.75/0.63    inference(ennf_transformation,[],[f15])).
% 1.75/0.63  fof(f15,negated_conjecture,(
% 1.75/0.63    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.75/0.63    inference(negated_conjecture,[],[f14])).
% 1.75/0.63  fof(f14,conjecture,(
% 1.75/0.63    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.75/0.63  fof(f108,plain,(
% 1.75/0.63    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 1.75/0.63    inference(equality_resolution,[],[f95])).
% 1.75/0.63  fof(f95,plain,(
% 1.75/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 1.75/0.63    inference(definition_unfolding,[],[f61,f75])).
% 1.75/0.63  fof(f61,plain,(
% 1.75/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.75/0.63    inference(cnf_transformation,[],[f37])).
% 1.75/0.63  fof(f37,plain,(
% 1.75/0.63    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.75/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 1.75/0.63  fof(f36,plain,(
% 1.75/0.63    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.75/0.63    introduced(choice_axiom,[])).
% 1.75/0.63  fof(f35,plain,(
% 1.75/0.63    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.75/0.63    inference(rectify,[],[f34])).
% 1.75/0.63  fof(f34,plain,(
% 1.75/0.63    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.75/0.63    inference(flattening,[],[f33])).
% 1.75/0.63  fof(f33,plain,(
% 1.75/0.63    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.75/0.63    inference(nnf_transformation,[],[f2])).
% 1.75/0.63  fof(f2,axiom,(
% 1.75/0.63    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.75/0.63  fof(f656,plain,(
% 1.75/0.63    ~r2_hidden(sK0,k1_xboole_0) | spl6_29),
% 1.75/0.63    inference(avatar_component_clause,[],[f655])).
% 1.75/0.63  fof(f655,plain,(
% 1.75/0.63    spl6_29 <=> r2_hidden(sK0,k1_xboole_0)),
% 1.75/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 1.75/0.63  fof(f657,plain,(
% 1.75/0.63    spl6_26 | ~spl6_29 | spl6_1 | ~spl6_3),
% 1.75/0.63    inference(avatar_split_clause,[],[f653,f121,f114,f655,f641])).
% 1.75/0.63  fof(f653,plain,(
% 1.75/0.63    ~r2_hidden(sK0,k1_xboole_0) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | (spl6_1 | ~spl6_3)),
% 1.75/0.63    inference(trivial_inequality_removal,[],[f652])).
% 1.75/0.63  fof(f652,plain,(
% 1.75/0.63    ~r2_hidden(sK0,k1_xboole_0) | sK0 != sK0 | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | (spl6_1 | ~spl6_3)),
% 1.75/0.63    inference(superposition,[],[f82,f602])).
% 1.75/0.63  fof(f602,plain,(
% 1.75/0.63    sK0 = sK4(sK0,k1_xboole_0) | (spl6_1 | ~spl6_3)),
% 1.75/0.63    inference(trivial_inequality_removal,[],[f601])).
% 1.75/0.63  fof(f601,plain,(
% 1.75/0.63    k1_xboole_0 != k1_xboole_0 | sK0 = sK4(sK0,k1_xboole_0) | (spl6_1 | ~spl6_3)),
% 1.75/0.63    inference(duplicate_literal_removal,[],[f571])).
% 1.75/0.63  fof(f571,plain,(
% 1.75/0.63    k1_xboole_0 != k1_xboole_0 | sK0 = sK4(sK0,k1_xboole_0) | sK0 = sK4(sK0,k1_xboole_0) | (spl6_1 | ~spl6_3)),
% 1.75/0.63    inference(superposition,[],[f292,f246])).
% 1.75/0.63  fof(f246,plain,(
% 1.75/0.63    ( ! [X3] : (k1_xboole_0 = k3_enumset1(X3,X3,X3,X3,X3) | sK4(X3,k1_xboole_0) = X3 | sK0 = sK4(X3,k1_xboole_0)) ) | ~spl6_3),
% 1.75/0.63    inference(resolution,[],[f227,f83])).
% 1.75/0.63  fof(f83,plain,(
% 1.75/0.63    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | sK4(X0,X1) = X0 | k3_enumset1(X0,X0,X0,X0,X0) = X1) )),
% 1.75/0.63    inference(definition_unfolding,[],[f54,f76])).
% 1.75/0.63  fof(f54,plain,(
% 1.75/0.63    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)) )),
% 1.75/0.63    inference(cnf_transformation,[],[f30])).
% 1.75/0.63  fof(f227,plain,(
% 1.75/0.63    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | sK0 = X0) ) | ~spl6_3),
% 1.75/0.63    inference(backward_demodulation,[],[f132,f180])).
% 1.75/0.63  fof(f132,plain,(
% 1.75/0.63    ( ! [X0] : (~r2_hidden(X0,sK1) | sK0 = X0) )),
% 1.75/0.63    inference(resolution,[],[f129,f103])).
% 1.75/0.63  fof(f103,plain,(
% 1.75/0.63    ( ! [X0,X3] : (~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.75/0.63    inference(equality_resolution,[],[f85])).
% 1.75/0.63  fof(f85,plain,(
% 1.75/0.63    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.75/0.63    inference(definition_unfolding,[],[f52,f76])).
% 1.75/0.63  fof(f52,plain,(
% 1.75/0.63    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.75/0.63    inference(cnf_transformation,[],[f30])).
% 1.75/0.63  fof(f129,plain,(
% 1.75/0.63    ( ! [X1] : (r2_hidden(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X1,sK1)) )),
% 1.75/0.63    inference(superposition,[],[f107,f80])).
% 1.75/0.63  fof(f107,plain,(
% 1.75/0.63    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 1.75/0.63    inference(equality_resolution,[],[f94])).
% 1.75/0.63  fof(f94,plain,(
% 1.75/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 1.75/0.63    inference(definition_unfolding,[],[f62,f75])).
% 1.75/0.63  fof(f62,plain,(
% 1.75/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 1.75/0.63    inference(cnf_transformation,[],[f37])).
% 1.75/0.63  fof(f82,plain,(
% 1.75/0.63    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | sK4(X0,X1) != X0 | k3_enumset1(X0,X0,X0,X0,X0) = X1) )),
% 1.75/0.63    inference(definition_unfolding,[],[f55,f76])).
% 1.75/0.63  fof(f55,plain,(
% 1.75/0.63    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) )),
% 1.75/0.63    inference(cnf_transformation,[],[f30])).
% 1.75/0.63  fof(f290,plain,(
% 1.75/0.63    spl6_4 | spl6_2),
% 1.75/0.63    inference(avatar_split_clause,[],[f285,f117,f124])).
% 1.75/0.63  fof(f124,plain,(
% 1.75/0.63    spl6_4 <=> sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.75/0.63    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.75/0.63  fof(f285,plain,(
% 1.75/0.63    k1_xboole_0 = sK2 | sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.75/0.63    inference(resolution,[],[f222,f88])).
% 1.75/0.63  fof(f88,plain,(
% 1.75/0.63    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 1.75/0.63    inference(definition_unfolding,[],[f56,f76,f76])).
% 1.75/0.63  fof(f56,plain,(
% 1.75/0.63    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.75/0.63    inference(cnf_transformation,[],[f32])).
% 1.75/0.63  fof(f32,plain,(
% 1.75/0.63    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.75/0.63    inference(flattening,[],[f31])).
% 1.75/0.63  fof(f31,plain,(
% 1.75/0.63    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.75/0.63    inference(nnf_transformation,[],[f11])).
% 1.75/0.63  fof(f11,axiom,(
% 1.75/0.63    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.75/0.63  fof(f222,plain,(
% 1.75/0.63    r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.75/0.63    inference(duplicate_literal_removal,[],[f220])).
% 1.75/0.63  fof(f220,plain,(
% 1.75/0.63    r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.75/0.63    inference(resolution,[],[f144,f50])).
% 1.75/0.63  fof(f50,plain,(
% 1.75/0.63    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.75/0.63    inference(cnf_transformation,[],[f26])).
% 1.75/0.63  fof(f26,plain,(
% 1.75/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.75/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 1.75/0.63  fof(f25,plain,(
% 1.75/0.63    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.75/0.63    introduced(choice_axiom,[])).
% 1.75/0.63  fof(f24,plain,(
% 1.75/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.75/0.63    inference(rectify,[],[f23])).
% 1.75/0.63  fof(f23,plain,(
% 1.75/0.63    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.75/0.63    inference(nnf_transformation,[],[f18])).
% 1.75/0.63  fof(f18,plain,(
% 1.75/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.75/0.63    inference(ennf_transformation,[],[f1])).
% 1.75/0.63  fof(f1,axiom,(
% 1.75/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.75/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.75/0.63  fof(f144,plain,(
% 1.75/0.63    ( ! [X1] : (~r2_hidden(sK3(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK2) | r1_tarski(X1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) )),
% 1.75/0.63    inference(resolution,[],[f130,f51])).
% 1.75/0.63  fof(f51,plain,(
% 1.75/0.63    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.75/0.63    inference(cnf_transformation,[],[f26])).
% 1.75/0.63  fof(f130,plain,(
% 1.75/0.63    ( ! [X2] : (r2_hidden(X2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X2,sK2)) )),
% 1.75/0.63    inference(superposition,[],[f106,f80])).
% 1.75/0.63  fof(f106,plain,(
% 1.75/0.63    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 1.75/0.63    inference(equality_resolution,[],[f93])).
% 1.75/0.63  fof(f93,plain,(
% 1.75/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 1.75/0.63    inference(definition_unfolding,[],[f63,f75])).
% 1.75/0.63  fof(f63,plain,(
% 1.75/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 1.75/0.63    inference(cnf_transformation,[],[f37])).
% 1.75/0.63  fof(f194,plain,(
% 1.75/0.63    spl6_3 | spl6_1),
% 1.75/0.63    inference(avatar_split_clause,[],[f193,f114,f121])).
% 1.75/0.63  fof(f193,plain,(
% 1.75/0.63    sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = sK1),
% 1.75/0.63    inference(global_subsumption,[],[f189])).
% 1.75/0.63  fof(f189,plain,(
% 1.75/0.63    k1_xboole_0 = sK1 | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.75/0.63    inference(resolution,[],[f151,f88])).
% 1.75/0.63  fof(f151,plain,(
% 1.75/0.63    ( ! [X1] : (r1_tarski(sK1,k3_enumset1(X1,X1,X1,X1,sK0))) )),
% 1.75/0.63    inference(resolution,[],[f131,f110])).
% 1.75/0.63  fof(f110,plain,(
% 1.75/0.63    ( ! [X2,X1] : (r1_tarski(k3_enumset1(X2,X2,X2,X2,X2),k3_enumset1(X1,X1,X1,X1,X2))) )),
% 1.75/0.63    inference(equality_resolution,[],[f97])).
% 1.75/0.63  fof(f97,plain,(
% 1.75/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2)) | k3_enumset1(X2,X2,X2,X2,X2) != X0) )),
% 1.75/0.63    inference(definition_unfolding,[],[f70,f74,f76])).
% 1.75/0.64  fof(f70,plain,(
% 1.75/0.64    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 1.75/0.64    inference(cnf_transformation,[],[f39])).
% 1.75/0.64  fof(f39,plain,(
% 1.75/0.64    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.75/0.64    inference(flattening,[],[f38])).
% 1.75/0.64  fof(f38,plain,(
% 1.75/0.64    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.75/0.64    inference(nnf_transformation,[],[f20])).
% 1.75/0.64  fof(f20,plain,(
% 1.75/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.75/0.64    inference(ennf_transformation,[],[f12])).
% 1.75/0.64  fof(f12,axiom,(
% 1.75/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.75/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.75/0.64  fof(f131,plain,(
% 1.75/0.64    ( ! [X3] : (~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X3) | r1_tarski(sK1,X3)) )),
% 1.75/0.64    inference(superposition,[],[f89,f80])).
% 1.75/0.64  fof(f89,plain,(
% 1.75/0.64    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 1.75/0.64    inference(definition_unfolding,[],[f60,f75])).
% 1.75/0.64  fof(f60,plain,(
% 1.75/0.64    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.75/0.64    inference(cnf_transformation,[],[f19])).
% 1.75/0.64  fof(f19,plain,(
% 1.75/0.64    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.75/0.64    inference(ennf_transformation,[],[f3])).
% 1.75/0.64  fof(f3,axiom,(
% 1.75/0.64    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.75/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.75/0.64  fof(f127,plain,(
% 1.75/0.64    ~spl6_1 | ~spl6_4),
% 1.75/0.64    inference(avatar_split_clause,[],[f79,f124,f114])).
% 1.75/0.64  fof(f79,plain,(
% 1.75/0.64    sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.75/0.64    inference(definition_unfolding,[],[f41,f76,f76])).
% 1.75/0.64  fof(f41,plain,(
% 1.75/0.64    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.75/0.64    inference(cnf_transformation,[],[f22])).
% 1.75/0.64  fof(f126,plain,(
% 1.75/0.64    ~spl6_3 | ~spl6_4),
% 1.75/0.64    inference(avatar_split_clause,[],[f78,f124,f121])).
% 1.75/0.64  fof(f78,plain,(
% 1.75/0.64    sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 1.75/0.64    inference(definition_unfolding,[],[f42,f76])).
% 1.75/0.64  fof(f42,plain,(
% 1.75/0.64    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.75/0.64    inference(cnf_transformation,[],[f22])).
% 1.75/0.64  fof(f119,plain,(
% 1.75/0.64    ~spl6_1 | ~spl6_2),
% 1.75/0.64    inference(avatar_split_clause,[],[f77,f117,f114])).
% 1.75/0.64  fof(f77,plain,(
% 1.75/0.64    k1_xboole_0 != sK2 | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.75/0.64    inference(definition_unfolding,[],[f43,f76])).
% 1.75/0.64  fof(f43,plain,(
% 1.75/0.64    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 1.75/0.64    inference(cnf_transformation,[],[f22])).
% 1.75/0.64  % SZS output end Proof for theBenchmark
% 1.75/0.64  % (6877)------------------------------
% 1.75/0.64  % (6877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.64  % (6877)Termination reason: Refutation
% 1.75/0.64  
% 1.75/0.64  % (6877)Memory used [KB]: 11129
% 1.75/0.64  % (6877)Time elapsed: 0.212 s
% 1.75/0.64  % (6877)------------------------------
% 1.75/0.64  % (6877)------------------------------
% 1.75/0.64  % (6900)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.75/0.64  % (6874)Success in time 0.275 s
%------------------------------------------------------------------------------
