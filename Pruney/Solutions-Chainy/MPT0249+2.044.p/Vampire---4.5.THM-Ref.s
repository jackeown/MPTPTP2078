%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 131 expanded)
%              Number of leaves         :   24 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  312 ( 438 expanded)
%              Number of equality atoms :  110 ( 204 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f301,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f102,f117,f139,f148,f207,f298,f300])).

fof(f300,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0)
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f298,plain,
    ( spl6_7
    | ~ spl6_10
    | ~ spl6_15 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | spl6_7
    | ~ spl6_10
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f290,f111])).

fof(f111,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl6_7
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f290,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl6_10
    | ~ spl6_15 ),
    inference(resolution,[],[f255,f206])).

fof(f206,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl6_15
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl6_10 ),
    inference(superposition,[],[f188,f147])).

fof(f147,plain,
    ( sK1 = k1_tarski(sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl6_10
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f188,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f61,f56])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f207,plain,
    ( spl6_15
    | spl6_1
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f202,f136,f73,f204])).

fof(f73,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f136,plain,
    ( spl6_9
  <=> sK0 = sK3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f202,plain,
    ( r2_hidden(sK0,sK2)
    | spl6_1
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f201,f75])).

fof(f75,plain,
    ( k1_xboole_0 != sK2
    | spl6_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f201,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ spl6_9 ),
    inference(superposition,[],[f43,f138])).

fof(f138,plain,
    ( sK0 = sK3(sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f148,plain,
    ( spl6_10
    | spl6_2
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f143,f99,f78,f145])).

fof(f78,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f99,plain,
    ( spl6_6
  <=> r1_tarski(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f143,plain,
    ( sK1 = k1_tarski(sK0)
    | spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f142,f80])).

fof(f80,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f142,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k1_tarski(sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f40,f101])).

fof(f101,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f139,plain,
    ( spl6_9
    | spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f134,f88,f73,f136])).

fof(f88,plain,
    ( spl6_4
  <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f134,plain,
    ( sK0 = sK3(sK2)
    | spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f133,f75])).

fof(f133,plain,
    ( sK0 = sK3(sK2)
    | k1_xboole_0 = sK2
    | ~ spl6_4 ),
    inference(resolution,[],[f129,f43])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | sK0 = X0 )
    | ~ spl6_4 ),
    inference(resolution,[],[f126,f71])).

fof(f71,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f126,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_tarski(sK0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl6_4 ),
    inference(superposition,[],[f66,f90])).

fof(f90,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f117,plain,
    ( ~ spl6_7
    | spl6_8
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f106,f88,f113,f109])).

fof(f113,plain,
    ( spl6_8
  <=> sK2 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f106,plain,
    ( sK2 = k1_tarski(sK0)
    | ~ r1_tarski(sK1,sK2)
    | ~ spl6_4 ),
    inference(superposition,[],[f90,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f102,plain,
    ( spl6_6
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f97,f88,f99])).

fof(f97,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl6_4 ),
    inference(superposition,[],[f58,f90])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f91,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f36,f88])).

fof(f36,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f86,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f37,f83])).

fof(f83,plain,
    ( spl6_3
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f37,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f20])).

fof(f81,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f38,f78])).

fof(f38,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f39,f73])).

fof(f39,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n011.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 10:26:12 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.51  % (5579)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (5572)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (5588)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (5595)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (5580)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (5587)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (5571)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (5588)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f301,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f102,f117,f139,f148,f207,f298,f300])).
% 0.21/0.55  fof(f300,plain,(
% 0.21/0.55    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0) | sK1 = sK2),
% 0.21/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.55  fof(f298,plain,(
% 0.21/0.55    spl6_7 | ~spl6_10 | ~spl6_15),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f297])).
% 0.21/0.55  fof(f297,plain,(
% 0.21/0.55    $false | (spl6_7 | ~spl6_10 | ~spl6_15)),
% 0.21/0.55    inference(subsumption_resolution,[],[f290,f111])).
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    ~r1_tarski(sK1,sK2) | spl6_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f109])).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    spl6_7 <=> r1_tarski(sK1,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.55  fof(f290,plain,(
% 0.21/0.55    r1_tarski(sK1,sK2) | (~spl6_10 | ~spl6_15)),
% 0.21/0.55    inference(resolution,[],[f255,f206])).
% 0.21/0.55  fof(f206,plain,(
% 0.21/0.55    r2_hidden(sK0,sK2) | ~spl6_15),
% 0.21/0.55    inference(avatar_component_clause,[],[f204])).
% 0.21/0.55  fof(f204,plain,(
% 0.21/0.55    spl6_15 <=> r2_hidden(sK0,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.55  fof(f255,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(sK0,X0) | r1_tarski(sK1,X0)) ) | ~spl6_10),
% 0.21/0.55    inference(superposition,[],[f188,f147])).
% 0.21/0.55  fof(f147,plain,(
% 0.21/0.55    sK1 = k1_tarski(sK0) | ~spl6_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f145])).
% 0.21/0.55  fof(f145,plain,(
% 0.21/0.55    spl6_10 <=> sK1 = k1_tarski(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.55  fof(f188,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f187])).
% 0.21/0.55  fof(f187,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(superposition,[],[f61,f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.55    inference(flattening,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.55    inference(nnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.55  fof(f207,plain,(
% 0.21/0.55    spl6_15 | spl6_1 | ~spl6_9),
% 0.21/0.55    inference(avatar_split_clause,[],[f202,f136,f73,f204])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    spl6_1 <=> k1_xboole_0 = sK2),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    spl6_9 <=> sK0 = sK3(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.55  fof(f202,plain,(
% 0.21/0.55    r2_hidden(sK0,sK2) | (spl6_1 | ~spl6_9)),
% 0.21/0.55    inference(subsumption_resolution,[],[f201,f75])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    k1_xboole_0 != sK2 | spl6_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f73])).
% 0.21/0.55  fof(f201,plain,(
% 0.21/0.55    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2 | ~spl6_9),
% 0.21/0.55    inference(superposition,[],[f43,f138])).
% 0.21/0.55  fof(f138,plain,(
% 0.21/0.55    sK0 = sK3(sK2) | ~spl6_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f136])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.55  fof(f148,plain,(
% 0.21/0.55    spl6_10 | spl6_2 | ~spl6_6),
% 0.21/0.55    inference(avatar_split_clause,[],[f143,f99,f78,f145])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    spl6_2 <=> k1_xboole_0 = sK1),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    spl6_6 <=> r1_tarski(sK1,k1_tarski(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.55  fof(f143,plain,(
% 0.21/0.55    sK1 = k1_tarski(sK0) | (spl6_2 | ~spl6_6)),
% 0.21/0.55    inference(subsumption_resolution,[],[f142,f80])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    k1_xboole_0 != sK1 | spl6_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f78])).
% 0.21/0.55  fof(f142,plain,(
% 0.21/0.55    k1_xboole_0 = sK1 | sK1 = k1_tarski(sK0) | ~spl6_6),
% 0.21/0.55    inference(resolution,[],[f40,f101])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    r1_tarski(sK1,k1_tarski(sK0)) | ~spl6_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f99])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.55    inference(flattening,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.55    inference(nnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    spl6_9 | spl6_1 | ~spl6_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f134,f88,f73,f136])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    spl6_4 <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.55  fof(f134,plain,(
% 0.21/0.55    sK0 = sK3(sK2) | (spl6_1 | ~spl6_4)),
% 0.21/0.55    inference(subsumption_resolution,[],[f133,f75])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    sK0 = sK3(sK2) | k1_xboole_0 = sK2 | ~spl6_4),
% 0.21/0.55    inference(resolution,[],[f129,f43])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,sK2) | sK0 = X0) ) | ~spl6_4),
% 0.21/0.55    inference(resolution,[],[f126,f71])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.21/0.55    inference(equality_resolution,[],[f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.55    inference(rectify,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(X0,k1_tarski(sK0)) | ~r2_hidden(X0,sK2)) ) | ~spl6_4),
% 0.21/0.55    inference(superposition,[],[f66,f90])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) | ~spl6_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f88])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.21/0.55    inference(equality_resolution,[],[f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(rectify,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(flattening,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.55    inference(nnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    ~spl6_7 | spl6_8 | ~spl6_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f106,f88,f113,f109])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    spl6_8 <=> sK2 = k1_tarski(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    sK2 = k1_tarski(sK0) | ~r1_tarski(sK1,sK2) | ~spl6_4),
% 0.21/0.55    inference(superposition,[],[f90,f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    spl6_6 | ~spl6_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f97,f88,f99])).
% 0.21/0.55  fof(f97,plain,(
% 0.21/0.55    r1_tarski(sK1,k1_tarski(sK0)) | ~spl6_4),
% 0.21/0.55    inference(superposition,[],[f58,f90])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    spl6_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f36,f88])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.55    inference(ennf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.55    inference(negated_conjecture,[],[f14])).
% 0.21/0.55  fof(f14,conjecture,(
% 0.21/0.55    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ~spl6_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f37,f83])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    spl6_3 <=> sK1 = sK2),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    sK1 != sK2),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    ~spl6_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f38,f78])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    k1_xboole_0 != sK1),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    ~spl6_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f39,f73])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    k1_xboole_0 != sK2),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (5588)------------------------------
% 0.21/0.55  % (5588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5588)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (5588)Memory used [KB]: 6396
% 0.21/0.55  % (5588)Time elapsed: 0.160 s
% 0.21/0.55  % (5588)------------------------------
% 0.21/0.55  % (5588)------------------------------
% 0.21/0.55  % (5566)Success in time 0.194 s
%------------------------------------------------------------------------------
