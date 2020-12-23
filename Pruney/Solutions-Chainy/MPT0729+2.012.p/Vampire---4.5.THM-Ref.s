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
% DateTime   : Thu Dec  3 12:55:12 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 300 expanded)
%              Number of leaves         :   17 (  97 expanded)
%              Depth                    :   16
%              Number of atoms          :  252 ( 705 expanded)
%              Number of equality atoms :   79 ( 347 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f402,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f40,f40,f40,f387,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | X0 = X2
      | X0 = X3
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP2(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP2(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP2(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP2(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X4,X2,X1,X0] :
      ( sP2(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f387,plain,(
    sP2(sK4,sK5,sK5,sK5) ),
    inference(resolution,[],[f384,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
      | sP2(X0,X3,X2,X1) ) ),
    inference(resolution,[],[f57,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] : sP3(X0,X1,X2,k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f65,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP3(X0,X1,X2,X3) )
      & ( sP3(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP3(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f14,f19,f18])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( sP3(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP2(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP3(X0,X1,X2,X3)
      | ~ r2_hidden(X5,X3)
      | sP2(X5,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

% (22569)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ( ( ~ sP2(sK7(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
          & ( sP2(sK7(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP2(X5,X2,X1,X0) )
            & ( sP2(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP2(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP2(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP2(sK7(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK7(X0,X1,X2,X3),X3) )
        & ( sP2(sK7(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK7(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP2(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP2(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP2(X5,X2,X1,X0) )
            & ( sP2(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP2(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP2(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP2(X4,X2,X1,X0) )
            & ( sP2(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f384,plain,(
    r2_hidden(sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(subsumption_resolution,[],[f382,f226])).

fof(f226,plain,(
    ~ r2_hidden(sK4,sK5) ),
    inference(resolution,[],[f198,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f198,plain,(
    r2_hidden(sK5,sK4) ),
    inference(subsumption_resolution,[],[f197,f40])).

fof(f197,plain,
    ( r2_hidden(sK5,sK4)
    | sK4 = sK5 ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,
    ( r2_hidden(sK5,sK4)
    | sK4 = sK5
    | sK4 = sK5
    | sK4 = sK5 ),
    inference(resolution,[],[f179,f61])).

fof(f179,plain,
    ( sP2(sK5,sK4,sK4,sK4)
    | r2_hidden(sK5,sK4) ),
    inference(resolution,[],[f145,f96])).

fof(f145,plain,
    ( r2_hidden(sK5,k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK5,sK4) ),
    inference(resolution,[],[f128,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r2_hidden(X1,X0)
          & ~ r2_hidden(X1,X2) ) )
      & ( r2_hidden(X1,X0)
        | r2_hidden(X1,X2)
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X3,X0) ) )
      & ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0)
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        | r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f128,plain,(
    sP0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK4) ),
    inference(resolution,[],[f116,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | sP0(X2,X0,X1) ) ),
    inference(resolution,[],[f48,f77])).

fof(f77,plain,(
    ! [X0,X1] : sP1(X0,X1,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f55,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f16,f15])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sP0(X1,sK6(X0,X1,X2),X0)
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sP0(X1,sK6(X0,X1,X2),X0)
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f116,plain,(
    r2_hidden(sK5,k3_tarski(k2_enumset1(sK4,sK4,sK4,k2_enumset1(sK4,sK4,sK4,sK4)))) ),
    inference(superposition,[],[f72,f71])).

fof(f71,plain,(
    k3_tarski(k2_enumset1(sK4,sK4,sK4,k2_enumset1(sK4,sK4,sK4,sK4))) = k3_tarski(k2_enumset1(sK5,sK5,sK5,k2_enumset1(sK5,sK5,sK5,sK5))) ),
    inference(definition_unfolding,[],[f39,f70,f70])).

fof(f70,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f43,f68,f69])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f67])).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f39,plain,(
    k1_ordinal1(sK4) = k1_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK4 != sK5
    & k1_ordinal1(sK4) = k1_ordinal1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f12,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_ordinal1(X0) = k1_ordinal1(X1) )
   => ( sK4 != sK5
      & k1_ordinal1(sK4) = k1_ordinal1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_ordinal1(X0) = k1_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_ordinal1(X0) = k1_ordinal1(X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k1_ordinal1(X0) = k1_ordinal1(X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).

fof(f72,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f41,f70])).

fof(f41,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f382,plain,
    ( r2_hidden(sK4,sK5)
    | r2_hidden(sK4,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(resolution,[],[f381,f52])).

fof(f381,plain,(
    sP0(k2_enumset1(sK5,sK5,sK5,sK5),sK4,sK5) ),
    inference(resolution,[],[f365,f81])).

fof(f365,plain,(
    ! [X0] :
      ( ~ sP3(sK5,sK5,sK5,X0)
      | sP0(X0,sK4,sK5) ) ),
    inference(resolution,[],[f210,f84])).

fof(f210,plain,(
    ! [X5] :
      ( r2_hidden(sK4,k3_tarski(k2_enumset1(sK5,sK5,sK5,X5)))
      | ~ sP3(sK5,sK5,sK5,X5) ) ),
    inference(superposition,[],[f72,f113])).

fof(f113,plain,(
    ! [X0] :
      ( k3_tarski(k2_enumset1(sK4,sK4,sK4,k2_enumset1(sK4,sK4,sK4,sK4))) = k3_tarski(k2_enumset1(sK5,sK5,sK5,X0))
      | ~ sP3(sK5,sK5,sK5,X0) ) ),
    inference(superposition,[],[f71,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(definition_unfolding,[],[f66,f47])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f40,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (22563)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.42/0.53  % (22571)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.42/0.53  % (22579)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.60/0.56  % (22559)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.60/0.57  % (22554)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.60/0.57  % (22559)Refutation not found, incomplete strategy% (22559)------------------------------
% 1.60/0.57  % (22559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (22564)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.60/0.57  % (22572)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.60/0.57  % (22577)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.60/0.58  % (22579)Refutation found. Thanks to Tanya!
% 1.60/0.58  % SZS status Theorem for theBenchmark
% 1.60/0.58  % (22552)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.60/0.58  % (22559)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.58  
% 1.60/0.58  % (22559)Memory used [KB]: 10618
% 1.60/0.58  % (22559)Time elapsed: 0.138 s
% 1.60/0.58  % (22559)------------------------------
% 1.60/0.58  % (22559)------------------------------
% 1.60/0.58  % (22561)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.60/0.58  % (22556)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.60/0.58  % (22561)Refutation not found, incomplete strategy% (22561)------------------------------
% 1.60/0.58  % (22561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (22561)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.58  
% 1.60/0.58  % (22561)Memory used [KB]: 10618
% 1.60/0.58  % (22561)Time elapsed: 0.178 s
% 1.60/0.58  % (22561)------------------------------
% 1.60/0.58  % (22561)------------------------------
% 1.60/0.58  % (22576)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.60/0.58  % SZS output start Proof for theBenchmark
% 1.60/0.59  fof(f402,plain,(
% 1.60/0.59    $false),
% 1.60/0.59    inference(unit_resulting_resolution,[],[f40,f40,f40,f387,f61])).
% 1.60/0.59  fof(f61,plain,(
% 1.60/0.59    ( ! [X2,X0,X3,X1] : (~sP2(X0,X1,X2,X3) | X0 = X2 | X0 = X3 | X0 = X1) )),
% 1.60/0.59    inference(cnf_transformation,[],[f37])).
% 1.60/0.59  fof(f37,plain,(
% 1.60/0.59    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP2(X0,X1,X2,X3)))),
% 1.60/0.59    inference(rectify,[],[f36])).
% 1.60/0.59  fof(f36,plain,(
% 1.60/0.59    ! [X4,X2,X1,X0] : ((sP2(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP2(X4,X2,X1,X0)))),
% 1.60/0.59    inference(flattening,[],[f35])).
% 1.60/0.59  fof(f35,plain,(
% 1.60/0.59    ! [X4,X2,X1,X0] : ((sP2(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP2(X4,X2,X1,X0)))),
% 1.60/0.59    inference(nnf_transformation,[],[f18])).
% 1.60/0.59  fof(f18,plain,(
% 1.60/0.59    ! [X4,X2,X1,X0] : (sP2(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 1.60/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.60/0.59  fof(f387,plain,(
% 1.60/0.59    sP2(sK4,sK5,sK5,sK5)),
% 1.60/0.59    inference(resolution,[],[f384,f96])).
% 1.60/0.59  fof(f96,plain,(
% 1.60/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) | sP2(X0,X3,X2,X1)) )),
% 1.60/0.59    inference(resolution,[],[f57,f81])).
% 1.60/0.59  fof(f81,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (sP3(X0,X1,X2,k2_enumset1(X0,X0,X1,X2))) )),
% 1.60/0.59    inference(equality_resolution,[],[f76])).
% 1.60/0.59  fof(f76,plain,(
% 1.60/0.59    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.60/0.59    inference(definition_unfolding,[],[f65,f47])).
% 1.60/0.59  fof(f47,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f6])).
% 1.60/0.59  fof(f6,axiom,(
% 1.60/0.59    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.60/0.59  fof(f65,plain,(
% 1.60/0.59    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.60/0.59    inference(cnf_transformation,[],[f38])).
% 1.60/0.59  fof(f38,plain,(
% 1.60/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP3(X0,X1,X2,X3)) & (sP3(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.60/0.59    inference(nnf_transformation,[],[f20])).
% 1.60/0.59  fof(f20,plain,(
% 1.60/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP3(X0,X1,X2,X3))),
% 1.60/0.59    inference(definition_folding,[],[f14,f19,f18])).
% 1.60/0.59  fof(f19,plain,(
% 1.60/0.59    ! [X0,X1,X2,X3] : (sP3(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP2(X4,X2,X1,X0)))),
% 1.60/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.60/0.59  fof(f14,plain,(
% 1.60/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.60/0.59    inference(ennf_transformation,[],[f3])).
% 1.60/0.59  fof(f3,axiom,(
% 1.60/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.60/0.59  fof(f57,plain,(
% 1.60/0.59    ( ! [X2,X0,X5,X3,X1] : (~sP3(X0,X1,X2,X3) | ~r2_hidden(X5,X3) | sP2(X5,X2,X1,X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f34])).
% 1.60/0.59  % (22569)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.60/0.59  fof(f34,plain,(
% 1.60/0.59    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ((~sP2(sK7(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sP2(sK7(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK7(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP2(X5,X2,X1,X0)) & (sP2(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP3(X0,X1,X2,X3)))),
% 1.60/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).
% 1.60/0.59  fof(f33,plain,(
% 1.60/0.59    ! [X3,X2,X1,X0] : (? [X4] : ((~sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP2(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP2(sK7(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK7(X0,X1,X2,X3),X3)) & (sP2(sK7(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK7(X0,X1,X2,X3),X3))))),
% 1.60/0.59    introduced(choice_axiom,[])).
% 1.60/0.59  fof(f32,plain,(
% 1.60/0.59    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ? [X4] : ((~sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP2(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP2(X5,X2,X1,X0)) & (sP2(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP3(X0,X1,X2,X3)))),
% 1.60/0.59    inference(rectify,[],[f31])).
% 1.60/0.59  fof(f31,plain,(
% 1.60/0.59    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | ? [X4] : ((~sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP2(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP2(X4,X2,X1,X0)) & (sP2(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP3(X0,X1,X2,X3)))),
% 1.60/0.59    inference(nnf_transformation,[],[f19])).
% 1.60/0.59  fof(f384,plain,(
% 1.60/0.59    r2_hidden(sK4,k2_enumset1(sK5,sK5,sK5,sK5))),
% 1.60/0.59    inference(subsumption_resolution,[],[f382,f226])).
% 1.60/0.59  fof(f226,plain,(
% 1.60/0.59    ~r2_hidden(sK4,sK5)),
% 1.60/0.59    inference(resolution,[],[f198,f46])).
% 1.60/0.59  fof(f46,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f13])).
% 1.60/0.59  fof(f13,plain,(
% 1.60/0.59    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.60/0.59    inference(ennf_transformation,[],[f1])).
% 1.60/0.59  fof(f1,axiom,(
% 1.60/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.60/0.59  fof(f198,plain,(
% 1.60/0.59    r2_hidden(sK5,sK4)),
% 1.60/0.59    inference(subsumption_resolution,[],[f197,f40])).
% 1.60/0.59  fof(f197,plain,(
% 1.60/0.59    r2_hidden(sK5,sK4) | sK4 = sK5),
% 1.60/0.59    inference(duplicate_literal_removal,[],[f196])).
% 1.60/0.59  fof(f196,plain,(
% 1.60/0.59    r2_hidden(sK5,sK4) | sK4 = sK5 | sK4 = sK5 | sK4 = sK5),
% 1.60/0.59    inference(resolution,[],[f179,f61])).
% 1.60/0.59  fof(f179,plain,(
% 1.60/0.59    sP2(sK5,sK4,sK4,sK4) | r2_hidden(sK5,sK4)),
% 1.60/0.59    inference(resolution,[],[f145,f96])).
% 1.60/0.59  fof(f145,plain,(
% 1.60/0.59    r2_hidden(sK5,k2_enumset1(sK4,sK4,sK4,sK4)) | r2_hidden(sK5,sK4)),
% 1.60/0.59    inference(resolution,[],[f128,f52])).
% 1.60/0.59  fof(f52,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2) | r2_hidden(X1,X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f29])).
% 1.60/0.59  fof(f29,plain,(
% 1.60/0.59    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r2_hidden(X1,X0) & ~r2_hidden(X1,X2))) & (r2_hidden(X1,X0) | r2_hidden(X1,X2) | ~sP0(X0,X1,X2)))),
% 1.60/0.59    inference(rectify,[],[f28])).
% 1.60/0.59  fof(f28,plain,(
% 1.60/0.59    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~sP0(X1,X3,X0)))),
% 1.60/0.59    inference(flattening,[],[f27])).
% 1.60/0.59  fof(f27,plain,(
% 1.60/0.59    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.60/0.59    inference(nnf_transformation,[],[f15])).
% 1.60/0.59  fof(f15,plain,(
% 1.60/0.59    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0)))),
% 1.60/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.60/0.59  fof(f128,plain,(
% 1.60/0.59    sP0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,sK4)),
% 1.60/0.59    inference(resolution,[],[f116,f84])).
% 1.60/0.59  fof(f84,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | sP0(X2,X0,X1)) )),
% 1.60/0.59    inference(resolution,[],[f48,f77])).
% 1.60/0.59  fof(f77,plain,(
% 1.60/0.59    ( ! [X0,X1] : (sP1(X0,X1,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.60/0.59    inference(equality_resolution,[],[f74])).
% 1.60/0.59  fof(f74,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 1.60/0.59    inference(definition_unfolding,[],[f55,f68])).
% 1.60/0.59  fof(f68,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.60/0.59    inference(definition_unfolding,[],[f44,f67])).
% 1.60/0.59  fof(f67,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.60/0.59    inference(definition_unfolding,[],[f45,f47])).
% 1.60/0.59  fof(f45,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f5])).
% 1.60/0.59  fof(f5,axiom,(
% 1.60/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.60/0.59  fof(f44,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f7])).
% 1.60/0.59  fof(f7,axiom,(
% 1.60/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.60/0.59  fof(f55,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.60/0.59    inference(cnf_transformation,[],[f30])).
% 1.60/0.59  fof(f30,plain,(
% 1.60/0.59    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k2_xboole_0(X0,X1) != X2))),
% 1.60/0.59    inference(nnf_transformation,[],[f17])).
% 1.60/0.59  fof(f17,plain,(
% 1.60/0.59    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 1.60/0.59    inference(definition_folding,[],[f2,f16,f15])).
% 1.60/0.59  fof(f16,plain,(
% 1.60/0.59    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 1.60/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.60/0.59  fof(f2,axiom,(
% 1.60/0.59    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.60/0.59  fof(f48,plain,(
% 1.60/0.59    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X1,X4,X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f26])).
% 1.60/0.59  fof(f26,plain,(
% 1.60/0.59    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(X1,sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.60/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f25])).
% 1.60/0.59  fof(f25,plain,(
% 1.60/0.59    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sP0(X1,sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.60/0.59    introduced(choice_axiom,[])).
% 1.60/0.59  fof(f24,plain,(
% 1.60/0.59    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.60/0.59    inference(rectify,[],[f23])).
% 1.60/0.59  fof(f23,plain,(
% 1.60/0.59    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 1.60/0.59    inference(nnf_transformation,[],[f16])).
% 1.60/0.59  fof(f116,plain,(
% 1.60/0.59    r2_hidden(sK5,k3_tarski(k2_enumset1(sK4,sK4,sK4,k2_enumset1(sK4,sK4,sK4,sK4))))),
% 1.60/0.59    inference(superposition,[],[f72,f71])).
% 1.60/0.59  fof(f71,plain,(
% 1.60/0.59    k3_tarski(k2_enumset1(sK4,sK4,sK4,k2_enumset1(sK4,sK4,sK4,sK4))) = k3_tarski(k2_enumset1(sK5,sK5,sK5,k2_enumset1(sK5,sK5,sK5,sK5)))),
% 1.60/0.59    inference(definition_unfolding,[],[f39,f70,f70])).
% 1.60/0.59  fof(f70,plain,(
% 1.60/0.59    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) )),
% 1.60/0.59    inference(definition_unfolding,[],[f43,f68,f69])).
% 1.60/0.59  fof(f69,plain,(
% 1.60/0.59    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.60/0.59    inference(definition_unfolding,[],[f42,f67])).
% 1.60/0.59  fof(f42,plain,(
% 1.60/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f4])).
% 1.60/0.59  fof(f4,axiom,(
% 1.60/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.60/0.59  fof(f43,plain,(
% 1.60/0.59    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f8])).
% 1.60/0.59  fof(f8,axiom,(
% 1.60/0.59    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.60/0.59  fof(f39,plain,(
% 1.60/0.59    k1_ordinal1(sK4) = k1_ordinal1(sK5)),
% 1.60/0.59    inference(cnf_transformation,[],[f22])).
% 1.60/0.59  fof(f22,plain,(
% 1.60/0.59    sK4 != sK5 & k1_ordinal1(sK4) = k1_ordinal1(sK5)),
% 1.60/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f12,f21])).
% 1.60/0.59  fof(f21,plain,(
% 1.60/0.59    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1)) => (sK4 != sK5 & k1_ordinal1(sK4) = k1_ordinal1(sK5))),
% 1.60/0.59    introduced(choice_axiom,[])).
% 1.60/0.59  fof(f12,plain,(
% 1.60/0.59    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1))),
% 1.60/0.59    inference(ennf_transformation,[],[f11])).
% 1.60/0.59  fof(f11,negated_conjecture,(
% 1.60/0.59    ~! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 1.60/0.59    inference(negated_conjecture,[],[f10])).
% 1.60/0.59  fof(f10,conjecture,(
% 1.60/0.59    ! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).
% 1.60/0.59  fof(f72,plain,(
% 1.60/0.59    ( ! [X0] : (r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0))))) )),
% 1.60/0.59    inference(definition_unfolding,[],[f41,f70])).
% 1.60/0.59  fof(f41,plain,(
% 1.60/0.59    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f9])).
% 1.60/0.59  fof(f9,axiom,(
% 1.60/0.59    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 1.60/0.59  fof(f382,plain,(
% 1.60/0.59    r2_hidden(sK4,sK5) | r2_hidden(sK4,k2_enumset1(sK5,sK5,sK5,sK5))),
% 1.60/0.59    inference(resolution,[],[f381,f52])).
% 1.60/0.59  fof(f381,plain,(
% 1.60/0.59    sP0(k2_enumset1(sK5,sK5,sK5,sK5),sK4,sK5)),
% 1.60/0.59    inference(resolution,[],[f365,f81])).
% 1.60/0.59  fof(f365,plain,(
% 1.60/0.59    ( ! [X0] : (~sP3(sK5,sK5,sK5,X0) | sP0(X0,sK4,sK5)) )),
% 1.60/0.59    inference(resolution,[],[f210,f84])).
% 1.60/0.59  fof(f210,plain,(
% 1.60/0.59    ( ! [X5] : (r2_hidden(sK4,k3_tarski(k2_enumset1(sK5,sK5,sK5,X5))) | ~sP3(sK5,sK5,sK5,X5)) )),
% 1.60/0.59    inference(superposition,[],[f72,f113])).
% 1.60/0.59  fof(f113,plain,(
% 1.60/0.59    ( ! [X0] : (k3_tarski(k2_enumset1(sK4,sK4,sK4,k2_enumset1(sK4,sK4,sK4,sK4))) = k3_tarski(k2_enumset1(sK5,sK5,sK5,X0)) | ~sP3(sK5,sK5,sK5,X0)) )),
% 1.60/0.59    inference(superposition,[],[f71,f75])).
% 1.60/0.59  fof(f75,plain,(
% 1.60/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | ~sP3(X0,X1,X2,X3)) )),
% 1.60/0.59    inference(definition_unfolding,[],[f66,f47])).
% 1.60/0.59  fof(f66,plain,(
% 1.60/0.59    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | ~sP3(X0,X1,X2,X3)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f38])).
% 1.60/0.59  fof(f40,plain,(
% 1.60/0.59    sK4 != sK5),
% 1.60/0.59    inference(cnf_transformation,[],[f22])).
% 1.60/0.59  % SZS output end Proof for theBenchmark
% 1.60/0.59  % (22579)------------------------------
% 1.60/0.59  % (22579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.59  % (22579)Termination reason: Refutation
% 1.60/0.59  
% 1.60/0.59  % (22579)Memory used [KB]: 1918
% 1.60/0.59  % (22579)Time elapsed: 0.154 s
% 1.60/0.59  % (22579)------------------------------
% 1.60/0.59  % (22579)------------------------------
% 1.60/0.59  % (22568)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.60/0.59  % (22548)Success in time 0.236 s
%------------------------------------------------------------------------------
