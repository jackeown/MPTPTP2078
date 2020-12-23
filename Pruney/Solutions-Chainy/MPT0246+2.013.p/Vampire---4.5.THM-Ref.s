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
% DateTime   : Thu Dec  3 12:37:46 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 141 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :   16
%              Number of atoms          :  233 ( 394 expanded)
%              Number of equality atoms :   68 ( 174 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f249,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f171,f248])).

fof(f248,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f246,f103])).

fof(f103,plain,
    ( ~ r1_tarski(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl5_3
  <=> r1_tarski(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f246,plain,(
    r1_tarski(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(trivial_inequality_removal,[],[f240])).

fof(f240,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(superposition,[],[f45,f230])).

fof(f230,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(resolution,[],[f223,f123])).

fof(f123,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ),
    inference(resolution,[],[f64,f68])).

fof(f68,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f41,f39])).

fof(f39,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f60])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f223,plain,(
    ! [X1] :
      ( r2_hidden(sK2,k4_xboole_0(sK1,X1))
      | k1_xboole_0 = k4_xboole_0(sK1,X1) ) ),
    inference(duplicate_literal_removal,[],[f222])).

fof(f222,plain,(
    ! [X1] :
      ( r2_hidden(sK2,k4_xboole_0(sK1,X1))
      | k1_xboole_0 = k4_xboole_0(sK1,X1)
      | k1_xboole_0 = k4_xboole_0(sK1,X1) ) ),
    inference(superposition,[],[f38,f126])).

fof(f126,plain,(
    ! [X0] :
      ( sK2 = sK3(k4_xboole_0(sK1,X0))
      | k1_xboole_0 = k4_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f119,f36])).

fof(f36,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | sK2 = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ! [X2] :
        ( sK2 = X2
        | ~ r2_hidden(X2,sK1) )
    & k1_xboole_0 != sK1
    & sK1 != k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( X1 = X2
            | ~ r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 )
   => ( ! [X2] :
          ( sK2 = X2
          | ~ r2_hidden(X2,sK1) )
      & k1_xboole_0 != sK1
      & sK1 != k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f119,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k4_xboole_0(X0,X1)),X0)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f112,f38])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f51,f67])).

fof(f67,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f18])).

fof(f18,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f171,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl5_4 ),
    inference(subsumption_resolution,[],[f168,f107])).

fof(f107,plain,
    ( ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl5_4
  <=> r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f168,plain,(
    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
    inference(trivial_inequality_removal,[],[f162])).

fof(f162,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
    inference(superposition,[],[f45,f144])).

fof(f144,plain,(
    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
    inference(resolution,[],[f62,f73])).

fof(f73,plain,(
    r2_hidden(sK2,sK1) ),
    inference(subsumption_resolution,[],[f72,f35])).

fof(f35,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f72,plain,
    ( r2_hidden(sK2,sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f38,f71])).

fof(f71,plain,(
    sK2 = sK3(sK1) ),
    inference(subsumption_resolution,[],[f70,f35])).

fof(f70,plain,
    ( k1_xboole_0 = sK1
    | sK2 = sK3(sK1) ),
    inference(resolution,[],[f38,f36])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f48,f60])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f109,plain,
    ( ~ spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f86,f101,f105])).

fof(f86,plain,
    ( ~ r1_tarski(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
    inference(extensionality_resolution,[],[f44,f61])).

fof(f61,plain,(
    sK1 != k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f34,f60])).

fof(f34,plain,(
    sK1 != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 20:49:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (822312961)
% 0.21/0.37  ipcrm: permission denied for id (822345734)
% 0.21/0.43  ipcrm: permission denied for id (822378550)
% 0.21/0.47  ipcrm: permission denied for id (822444115)
% 0.21/0.49  ipcrm: permission denied for id (822509665)
% 0.21/0.51  ipcrm: permission denied for id (822607990)
% 0.51/0.64  % (23966)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.99/0.65  % (23982)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.99/0.66  % (23966)Refutation found. Thanks to Tanya!
% 0.99/0.66  % SZS status Theorem for theBenchmark
% 0.99/0.66  % SZS output start Proof for theBenchmark
% 0.99/0.66  fof(f249,plain,(
% 0.99/0.66    $false),
% 0.99/0.66    inference(avatar_sat_refutation,[],[f109,f171,f248])).
% 0.99/0.66  fof(f248,plain,(
% 0.99/0.66    spl5_3),
% 0.99/0.66    inference(avatar_contradiction_clause,[],[f247])).
% 0.99/0.66  fof(f247,plain,(
% 0.99/0.66    $false | spl5_3),
% 0.99/0.66    inference(subsumption_resolution,[],[f246,f103])).
% 0.99/0.66  fof(f103,plain,(
% 0.99/0.66    ~r1_tarski(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) | spl5_3),
% 0.99/0.66    inference(avatar_component_clause,[],[f101])).
% 0.99/0.66  fof(f101,plain,(
% 0.99/0.66    spl5_3 <=> r1_tarski(sK1,k2_enumset1(sK2,sK2,sK2,sK2))),
% 0.99/0.66    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.99/0.66  fof(f246,plain,(
% 0.99/0.66    r1_tarski(sK1,k2_enumset1(sK2,sK2,sK2,sK2))),
% 0.99/0.66    inference(trivial_inequality_removal,[],[f240])).
% 0.99/0.66  fof(f240,plain,(
% 0.99/0.66    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,k2_enumset1(sK2,sK2,sK2,sK2))),
% 0.99/0.66    inference(superposition,[],[f45,f230])).
% 1.16/0.66  fof(f230,plain,(
% 1.16/0.66    k1_xboole_0 = k4_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))),
% 1.16/0.66    inference(resolution,[],[f223,f123])).
% 1.16/0.66  fof(f123,plain,(
% 1.16/0.66    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) )),
% 1.16/0.66    inference(resolution,[],[f64,f68])).
% 1.16/0.66  fof(f68,plain,(
% 1.16/0.66    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.16/0.66    inference(resolution,[],[f41,f39])).
% 1.16/0.66  fof(f39,plain,(
% 1.16/0.66    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.16/0.66    inference(cnf_transformation,[],[f6])).
% 1.16/0.66  fof(f6,axiom,(
% 1.16/0.66    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.16/0.66  fof(f41,plain,(
% 1.16/0.66    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.16/0.66    inference(cnf_transformation,[],[f16])).
% 1.16/0.66  fof(f16,plain,(
% 1.16/0.66    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.16/0.66    inference(ennf_transformation,[],[f2])).
% 1.16/0.66  fof(f2,axiom,(
% 1.16/0.66    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.16/0.66  fof(f64,plain,(
% 1.16/0.66    ( ! [X0,X1] : (~r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.16/0.66    inference(definition_unfolding,[],[f49,f60])).
% 1.16/0.66  fof(f60,plain,(
% 1.16/0.66    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.16/0.66    inference(definition_unfolding,[],[f37,f59])).
% 1.16/0.66  fof(f59,plain,(
% 1.16/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.16/0.66    inference(definition_unfolding,[],[f40,f50])).
% 1.16/0.66  fof(f50,plain,(
% 1.16/0.66    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.16/0.66    inference(cnf_transformation,[],[f9])).
% 1.16/0.66  fof(f9,axiom,(
% 1.16/0.66    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.16/0.66  fof(f40,plain,(
% 1.16/0.66    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.16/0.66    inference(cnf_transformation,[],[f8])).
% 1.16/0.66  fof(f8,axiom,(
% 1.16/0.66    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.16/0.66  fof(f37,plain,(
% 1.16/0.66    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.16/0.66    inference(cnf_transformation,[],[f7])).
% 1.16/0.66  fof(f7,axiom,(
% 1.16/0.66    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.16/0.66  fof(f49,plain,(
% 1.16/0.66    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.16/0.66    inference(cnf_transformation,[],[f17])).
% 1.16/0.66  fof(f17,plain,(
% 1.16/0.66    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.16/0.66    inference(ennf_transformation,[],[f10])).
% 1.16/0.66  fof(f10,axiom,(
% 1.16/0.66    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.16/0.66  fof(f223,plain,(
% 1.16/0.66    ( ! [X1] : (r2_hidden(sK2,k4_xboole_0(sK1,X1)) | k1_xboole_0 = k4_xboole_0(sK1,X1)) )),
% 1.16/0.66    inference(duplicate_literal_removal,[],[f222])).
% 1.16/0.66  fof(f222,plain,(
% 1.16/0.66    ( ! [X1] : (r2_hidden(sK2,k4_xboole_0(sK1,X1)) | k1_xboole_0 = k4_xboole_0(sK1,X1) | k1_xboole_0 = k4_xboole_0(sK1,X1)) )),
% 1.16/0.66    inference(superposition,[],[f38,f126])).
% 1.16/0.66  fof(f126,plain,(
% 1.16/0.66    ( ! [X0] : (sK2 = sK3(k4_xboole_0(sK1,X0)) | k1_xboole_0 = k4_xboole_0(sK1,X0)) )),
% 1.16/0.66    inference(resolution,[],[f119,f36])).
% 1.16/0.66  fof(f36,plain,(
% 1.16/0.66    ( ! [X2] : (~r2_hidden(X2,sK1) | sK2 = X2) )),
% 1.16/0.66    inference(cnf_transformation,[],[f21])).
% 1.16/0.66  fof(f21,plain,(
% 1.16/0.66    ! [X2] : (sK2 = X2 | ~r2_hidden(X2,sK1)) & k1_xboole_0 != sK1 & sK1 != k1_tarski(sK2)),
% 1.16/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f20])).
% 1.16/0.66  fof(f20,plain,(
% 1.16/0.66    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0) => (! [X2] : (sK2 = X2 | ~r2_hidden(X2,sK1)) & k1_xboole_0 != sK1 & sK1 != k1_tarski(sK2))),
% 1.16/0.66    introduced(choice_axiom,[])).
% 1.16/0.66  fof(f14,plain,(
% 1.16/0.66    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.16/0.66    inference(ennf_transformation,[],[f13])).
% 1.16/0.66  fof(f13,negated_conjecture,(
% 1.16/0.66    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.16/0.66    inference(negated_conjecture,[],[f12])).
% 1.16/0.66  fof(f12,conjecture,(
% 1.16/0.66    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 1.16/0.66  fof(f119,plain,(
% 1.16/0.66    ( ! [X0,X1] : (r2_hidden(sK3(k4_xboole_0(X0,X1)),X0) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.16/0.66    inference(resolution,[],[f112,f38])).
% 1.16/0.66  fof(f112,plain,(
% 1.16/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | r2_hidden(X0,X1)) )),
% 1.16/0.66    inference(resolution,[],[f51,f67])).
% 1.16/0.66  fof(f67,plain,(
% 1.16/0.66    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 1.16/0.66    inference(equality_resolution,[],[f57])).
% 1.16/0.66  fof(f57,plain,(
% 1.16/0.66    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.16/0.66    inference(cnf_transformation,[],[f33])).
% 1.16/0.66  fof(f33,plain,(
% 1.16/0.66    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.16/0.66    inference(nnf_transformation,[],[f19])).
% 1.16/0.66  fof(f19,plain,(
% 1.16/0.66    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.16/0.66    inference(definition_folding,[],[f1,f18])).
% 1.16/0.66  fof(f18,plain,(
% 1.16/0.66    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.16/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.16/0.66  fof(f1,axiom,(
% 1.16/0.66    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.16/0.66  fof(f51,plain,(
% 1.16/0.66    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X1)) )),
% 1.16/0.66    inference(cnf_transformation,[],[f32])).
% 1.16/0.66  fof(f32,plain,(
% 1.16/0.66    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.16/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 1.16/0.66  fof(f31,plain,(
% 1.16/0.66    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.16/0.66    introduced(choice_axiom,[])).
% 1.16/0.66  fof(f30,plain,(
% 1.16/0.66    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.16/0.66    inference(rectify,[],[f29])).
% 1.16/0.66  fof(f29,plain,(
% 1.16/0.66    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.16/0.66    inference(flattening,[],[f28])).
% 1.16/0.66  fof(f28,plain,(
% 1.16/0.66    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.16/0.66    inference(nnf_transformation,[],[f18])).
% 1.16/0.66  fof(f38,plain,(
% 1.16/0.66    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.16/0.66    inference(cnf_transformation,[],[f23])).
% 1.16/0.66  fof(f23,plain,(
% 1.16/0.66    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.16/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f22])).
% 1.16/0.66  fof(f22,plain,(
% 1.16/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.16/0.66    introduced(choice_axiom,[])).
% 1.16/0.66  fof(f15,plain,(
% 1.16/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.16/0.66    inference(ennf_transformation,[],[f3])).
% 1.16/0.66  fof(f3,axiom,(
% 1.16/0.66    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.16/0.66  fof(f45,plain,(
% 1.16/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.16/0.66    inference(cnf_transformation,[],[f26])).
% 1.16/0.66  fof(f26,plain,(
% 1.16/0.66    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.16/0.66    inference(nnf_transformation,[],[f5])).
% 1.16/0.67  fof(f5,axiom,(
% 1.16/0.67    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.16/0.67  fof(f171,plain,(
% 1.16/0.67    spl5_4),
% 1.16/0.67    inference(avatar_contradiction_clause,[],[f170])).
% 1.16/0.67  fof(f170,plain,(
% 1.16/0.67    $false | spl5_4),
% 1.16/0.67    inference(subsumption_resolution,[],[f168,f107])).
% 1.16/0.67  fof(f107,plain,(
% 1.16/0.67    ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1) | spl5_4),
% 1.16/0.67    inference(avatar_component_clause,[],[f105])).
% 1.16/0.67  fof(f105,plain,(
% 1.16/0.67    spl5_4 <=> r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)),
% 1.16/0.67    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.16/0.67  fof(f168,plain,(
% 1.16/0.67    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)),
% 1.16/0.67    inference(trivial_inequality_removal,[],[f162])).
% 1.16/0.67  fof(f162,plain,(
% 1.16/0.67    k1_xboole_0 != k1_xboole_0 | r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)),
% 1.16/0.67    inference(superposition,[],[f45,f144])).
% 1.16/0.67  fof(f144,plain,(
% 1.16/0.67    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),sK1)),
% 1.16/0.67    inference(resolution,[],[f62,f73])).
% 1.16/0.67  fof(f73,plain,(
% 1.16/0.67    r2_hidden(sK2,sK1)),
% 1.16/0.67    inference(subsumption_resolution,[],[f72,f35])).
% 1.16/0.67  fof(f35,plain,(
% 1.16/0.67    k1_xboole_0 != sK1),
% 1.16/0.67    inference(cnf_transformation,[],[f21])).
% 1.16/0.67  fof(f72,plain,(
% 1.16/0.67    r2_hidden(sK2,sK1) | k1_xboole_0 = sK1),
% 1.16/0.67    inference(superposition,[],[f38,f71])).
% 1.16/0.67  fof(f71,plain,(
% 1.16/0.67    sK2 = sK3(sK1)),
% 1.16/0.67    inference(subsumption_resolution,[],[f70,f35])).
% 1.16/0.67  fof(f70,plain,(
% 1.16/0.67    k1_xboole_0 = sK1 | sK2 = sK3(sK1)),
% 1.16/0.67    inference(resolution,[],[f38,f36])).
% 1.16/0.67  fof(f62,plain,(
% 1.16/0.67    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 1.16/0.67    inference(definition_unfolding,[],[f48,f60])).
% 1.16/0.67  fof(f48,plain,(
% 1.16/0.67    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.16/0.67    inference(cnf_transformation,[],[f27])).
% 1.16/0.67  fof(f27,plain,(
% 1.16/0.67    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 1.16/0.67    inference(nnf_transformation,[],[f11])).
% 1.16/0.67  fof(f11,axiom,(
% 1.16/0.67    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 1.16/0.67  fof(f109,plain,(
% 1.16/0.67    ~spl5_4 | ~spl5_3),
% 1.16/0.67    inference(avatar_split_clause,[],[f86,f101,f105])).
% 1.16/0.67  fof(f86,plain,(
% 1.16/0.67    ~r1_tarski(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) | ~r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),sK1)),
% 1.16/0.67    inference(extensionality_resolution,[],[f44,f61])).
% 1.16/0.67  fof(f61,plain,(
% 1.16/0.67    sK1 != k2_enumset1(sK2,sK2,sK2,sK2)),
% 1.16/0.67    inference(definition_unfolding,[],[f34,f60])).
% 1.16/0.67  fof(f34,plain,(
% 1.16/0.67    sK1 != k1_tarski(sK2)),
% 1.16/0.67    inference(cnf_transformation,[],[f21])).
% 1.16/0.67  fof(f44,plain,(
% 1.16/0.67    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.16/0.67    inference(cnf_transformation,[],[f25])).
% 1.16/0.67  fof(f25,plain,(
% 1.16/0.67    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.16/0.67    inference(flattening,[],[f24])).
% 1.16/0.67  fof(f24,plain,(
% 1.16/0.67    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.16/0.67    inference(nnf_transformation,[],[f4])).
% 1.16/0.67  fof(f4,axiom,(
% 1.16/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.16/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.16/0.67  % SZS output end Proof for theBenchmark
% 1.16/0.67  % (23966)------------------------------
% 1.16/0.67  % (23966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.67  % (23966)Termination reason: Refutation
% 1.16/0.67  
% 1.16/0.67  % (23966)Memory used [KB]: 10874
% 1.16/0.67  % (23966)Time elapsed: 0.068 s
% 1.16/0.67  % (23966)------------------------------
% 1.16/0.67  % (23966)------------------------------
% 1.16/0.67  % (23734)Success in time 0.306 s
%------------------------------------------------------------------------------
