%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0153+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 (  87 expanded)
%              Number of leaves         :    9 (  24 expanded)
%              Depth                    :   17
%              Number of atoms          :  187 ( 341 expanded)
%              Number of equality atoms :   74 ( 132 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112,plain,(
    $false ),
    inference(subsumption_resolution,[],[f110,f43])).

fof(f43,plain,(
    ! [X0] : sP0(X0,k1_tarski(X0)) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f1,f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f110,plain,(
    ~ sP0(sK3,k1_tarski(sK3)) ),
    inference(resolution,[],[f106,f42])).

fof(f42,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ sP0(X3,X1) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f15])).

fof(f15,plain,(
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

fof(f14,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f106,plain,(
    ~ r2_hidden(sK3,k1_tarski(sK3)) ),
    inference(subsumption_resolution,[],[f102,f44])).

fof(f44,plain,(
    ! [X2,X1] : sP1(X1,X1,X2) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( X0 != X1
          & X0 != X2 ) )
      & ( X0 = X1
        | X0 = X2
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X3,X1,X0] :
      ( ( sP1(X3,X1,X0)
        | ( X1 != X3
          & X0 != X3 ) )
      & ( X1 = X3
        | X0 = X3
        | ~ sP1(X3,X1,X0) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X3,X1,X0] :
      ( ( sP1(X3,X1,X0)
        | ( X1 != X3
          & X0 != X3 ) )
      & ( X1 = X3
        | X0 = X3
        | ~ sP1(X3,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X3,X1,X0] :
      ( sP1(X3,X1,X0)
    <=> ( X1 = X3
        | X0 = X3 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f102,plain,
    ( ~ sP1(sK3,sK3,sK3)
    | ~ r2_hidden(sK3,k1_tarski(sK3)) ),
    inference(trivial_inequality_removal,[],[f94])).

fof(f94,plain,
    ( ~ sP1(sK3,sK3,sK3)
    | k1_tarski(sK3) != k1_tarski(sK3)
    | ~ r2_hidden(sK3,k1_tarski(sK3)) ),
    inference(superposition,[],[f49,f86])).

fof(f86,plain,(
    sK3 = sK5(sK3,sK3,k1_tarski(sK3)) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,
    ( sK3 = sK5(sK3,sK3,k1_tarski(sK3))
    | sK3 = sK5(sK3,sK3,k1_tarski(sK3)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4] :
      ( k1_tarski(sK3) != k1_tarski(X4)
      | sK5(sK3,sK3,k1_tarski(X4)) = X4
      | sK3 = sK5(sK3,sK3,k1_tarski(X4)) ) ),
    inference(resolution,[],[f56,f43])).

fof(f56,plain,(
    ! [X4,X3] :
      ( ~ sP0(X4,X3)
      | sK3 = sK5(sK3,sK3,X3)
      | sK5(sK3,sK3,X3) = X4
      | k1_tarski(sK3) != X3 ) ),
    inference(resolution,[],[f54,f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK3,sK3,X1),X1)
      | k1_tarski(sK3) != X1
      | sK3 = sK5(sK3,sK3,X1) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X1] :
      ( k1_tarski(sK3) != X1
      | r2_hidden(sK5(sK3,sK3,X1),X1)
      | sK3 = sK5(sK3,sK3,X1)
      | sK3 = sK5(sK3,sK3,X1) ) ),
    inference(resolution,[],[f48,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | X0 = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X0] :
      ( sP1(sK5(sK3,sK3,X0),sK3,sK3)
      | k1_tarski(sK3) != X0
      | r2_hidden(sK5(sK3,sK3,X0),X0) ) ),
    inference(resolution,[],[f47,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | sP1(sK5(X0,X1,X2),X1,X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ~ sP1(sK5(X0,X1,X2),X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sP1(sK5(X0,X1,X2),X1,X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X4,X1,X0) )
            & ( sP1(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP1(X3,X1,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP1(X3,X1,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP1(sK5(X0,X1,X2),X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sP1(sK5(X0,X1,X2),X1,X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X4,X1,X0) )
            & ( sP1(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP1(X3,X1,X0) )
            & ( sP1(X3,X1,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP1(X3,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f47,plain,(
    ! [X0] :
      ( ~ sP2(sK3,sK3,X0)
      | k1_tarski(sK3) != X0 ) ),
    inference(superposition,[],[f26,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP2(X0,X1,X2) )
      & ( sP2(X0,X1,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP2(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f9,f8])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f26,plain,(
    k1_tarski(sK3) != k2_tarski(sK3,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k1_tarski(sK3) != k2_tarski(sK3,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f5,f11])).

fof(f11,plain,
    ( ? [X0] : k1_tarski(X0) != k2_tarski(X0,X0)
   => k1_tarski(sK3) != k2_tarski(sK3,sK3) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] : k1_tarski(X0) != k2_tarski(X0,X0) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X1] :
      ( ~ sP1(sK5(sK3,sK3,X1),sK3,sK3)
      | k1_tarski(sK3) != X1
      | ~ r2_hidden(sK5(sK3,sK3,X1),X1) ) ),
    inference(resolution,[],[f47,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ sP1(sK5(X0,X1,X2),X1,X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------
