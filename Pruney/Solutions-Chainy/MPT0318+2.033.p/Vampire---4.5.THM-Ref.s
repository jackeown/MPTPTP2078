%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 682 expanded)
%              Number of leaves         :   13 ( 185 expanded)
%              Depth                    :   20
%              Number of atoms          :  265 (2424 expanded)
%              Number of equality atoms :  155 (1623 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f150,f165])).

fof(f165,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f163,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f163,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0)
    | ~ spl4_1
    | spl4_2 ),
    inference(forward_demodulation,[],[f68,f161])).

fof(f161,plain,
    ( k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f160,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( k1_xboole_0 = k2_zfmisc_1(sK1,k1_tarski(sK2))
      | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK2),sK1) )
    & k1_xboole_0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
          | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
        & k1_xboole_0 != X0 )
   => ( ( k1_xboole_0 = k2_zfmisc_1(sK1,k1_tarski(sK2))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK2),sK1) )
      & k1_xboole_0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f160,plain,
    ( k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | k1_xboole_0 = sK1
    | ~ spl4_1 ),
    inference(trivial_inequality_removal,[],[f159])).

fof(f159,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | k1_xboole_0 = sK1
    | ~ spl4_1 ),
    inference(superposition,[],[f30,f65])).

fof(f65,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_1
  <=> k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_2
  <=> k1_xboole_0 = k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f150,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f137,f133])).

fof(f133,plain,
    ( ! [X2,X1] : r2_hidden(X1,X2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f132,f108])).

fof(f108,plain,
    ( ! [X4] : sK2 = X4
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,
    ( ! [X4] :
        ( sK2 = X4
        | sK2 = X4
        | sK2 = X4 )
    | ~ spl4_2 ),
    inference(resolution,[],[f91,f100])).

fof(f100,plain,
    ( ! [X0] :
        ( r2_hidden(sK2,k2_enumset1(X0,X0,X0,X0))
        | sK2 = X0 )
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f97])).

fof(f97,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | r2_hidden(sK2,k2_enumset1(X0,X0,X0,X0))
        | sK2 = X0 )
    | ~ spl4_2 ),
    inference(superposition,[],[f89,f95])).

fof(f95,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_enumset1(X0,X0,X0,X0))
        | sK2 = X0 )
    | ~ spl4_2 ),
    inference(resolution,[],[f93,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f34,f48])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f93,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_xboole_0)
        | sK2 = X3 )
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,
    ( ! [X3] :
        ( sK2 = X3
        | ~ r2_hidden(X3,k1_xboole_0)
        | sK2 = X3 )
    | ~ spl4_2 ),
    inference(resolution,[],[f36,f83])).

fof(f83,plain,
    ( sP0(sK2,sK2,k1_xboole_0)
    | ~ spl4_2 ),
    inference(superposition,[],[f61,f79])).

fof(f79,plain,
    ( k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f78,f26])).

fof(f78,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f77])).

fof(f77,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ spl4_2 ),
    inference(superposition,[],[f30,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f61,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f11])).

fof(f11,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK3(X0,X1,X2) != X0
              & sK3(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X0
            | sK3(X0,X1,X2) = X1
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X0
            & sK3(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X0
          | sK3(X0,X1,X2) = X1
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f89,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0)
        | r2_hidden(sK2,X0) )
    | ~ spl4_2 ),
    inference(superposition,[],[f55,f79])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_enumset1(X0,X0,X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f36,f61])).

fof(f132,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != sK2
        | r2_hidden(X1,X2) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f110,f108])).

fof(f110,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != k4_xboole_0(sK2,X2)
        | r2_hidden(X1,X2) )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f55,f108])).

fof(f137,plain,
    ( ! [X0,X1] : ~ r2_hidden(X1,X0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f136,f108])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( sK2 != X0
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f118,f108])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,sK2) != X0
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f51,f108])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f33,f48])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f70,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f49,f67,f63])).

fof(f49,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK1) ),
    inference(definition_unfolding,[],[f27,f48,f48])).

fof(f27,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,k1_tarski(sK2))
    | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK2),sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:39:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (6364)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.49  % (6364)Refutation not found, incomplete strategy% (6364)------------------------------
% 0.20/0.49  % (6364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (6356)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (6364)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (6364)Memory used [KB]: 1663
% 0.20/0.49  % (6364)Time elapsed: 0.005 s
% 0.20/0.49  % (6364)------------------------------
% 0.20/0.49  % (6364)------------------------------
% 0.20/0.49  % (6356)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f70,f150,f165])).
% 0.20/0.49  fof(f165,plain,(
% 0.20/0.49    ~spl4_1 | spl4_2),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f164])).
% 0.20/0.49  fof(f164,plain,(
% 0.20/0.49    $false | (~spl4_1 | spl4_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f163,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.49    inference(flattening,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.49    inference(nnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.49  fof(f163,plain,(
% 0.20/0.49    k1_xboole_0 != k2_zfmisc_1(sK1,k1_xboole_0) | (~spl4_1 | spl4_2)),
% 0.20/0.49    inference(forward_demodulation,[],[f68,f161])).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | ~spl4_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f160,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    k1_xboole_0 != sK1),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    (k1_xboole_0 = k2_zfmisc_1(sK1,k1_tarski(sK2)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK2),sK1)) & k1_xboole_0 != sK1),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f10,f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0) => ((k1_xboole_0 = k2_zfmisc_1(sK1,k1_tarski(sK2)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK2),sK1)) & k1_xboole_0 != sK1)),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.20/0.49    inference(negated_conjecture,[],[f8])).
% 0.20/0.49  fof(f8,conjecture,(
% 0.20/0.49    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.20/0.49  fof(f160,plain,(
% 0.20/0.49    k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | k1_xboole_0 = sK1 | ~spl4_1),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f159])).
% 0.20/0.49  fof(f159,plain,(
% 0.20/0.49    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | k1_xboole_0 = sK1 | ~spl4_1),
% 0.20/0.49    inference(superposition,[],[f30,f65])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK1) | ~spl4_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    spl4_1 <=> k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    k1_xboole_0 != k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) | spl4_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f67])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    spl4_2 <=> k1_xboole_0 = k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    ~spl4_2),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f149])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    $false | ~spl4_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f137,f133])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    ( ! [X2,X1] : (r2_hidden(X1,X2)) ) | ~spl4_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f132,f108])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    ( ! [X4] : (sK2 = X4) ) | ~spl4_2),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f104])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ( ! [X4] : (sK2 = X4 | sK2 = X4 | sK2 = X4) ) | ~spl4_2),
% 0.20/0.49    inference(resolution,[],[f91,f100])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(sK2,k2_enumset1(X0,X0,X0,X0)) | sK2 = X0) ) | ~spl4_2),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f97])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r2_hidden(sK2,k2_enumset1(X0,X0,X0,X0)) | sK2 = X0) ) | ~spl4_2),
% 0.20/0.49    inference(superposition,[],[f89,f95])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) | sK2 = X0) ) | ~spl4_2),
% 0.20/0.49    inference(resolution,[],[f93,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0) )),
% 0.20/0.49    inference(definition_unfolding,[],[f34,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f28,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f29,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0) | sK2 = X3) ) | ~spl4_2),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f92])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    ( ! [X3] : (sK2 = X3 | ~r2_hidden(X3,k1_xboole_0) | sK2 = X3) ) | ~spl4_2),
% 0.20/0.49    inference(resolution,[],[f36,f83])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    sP0(sK2,sK2,k1_xboole_0) | ~spl4_2),
% 0.20/0.49    inference(superposition,[],[f61,f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | ~spl4_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f78,f26])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | ~spl4_2),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | ~spl4_2),
% 0.20/0.49    inference(superposition,[],[f30,f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    k1_xboole_0 = k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) | ~spl4_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f67])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sP0(X1,X0,k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.49    inference(equality_resolution,[],[f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.20/0.49    inference(definition_unfolding,[],[f42,f47])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 0.20/0.49    inference(nnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.20/0.49    inference(definition_folding,[],[f1,f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK3(X0,X1,X2) != X0 & sK3(X0,X1,X2) != X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X0 | sK3(X0,X1,X2) = X1 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X0 & sK3(X0,X1,X2) != X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X0 | sK3(X0,X1,X2) = X1 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.49    inference(rectify,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.20/0.49    inference(nnf_transformation,[],[f11])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0) | r2_hidden(sK2,X0)) ) | ~spl4_2),
% 0.20/0.49    inference(superposition,[],[f55,f79])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_xboole_0 != k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f45,f47])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.20/0.49    inference(flattening,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.20/0.49    inference(nnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_enumset1(X0,X0,X0,X2)) | X0 = X1 | X1 = X2) )),
% 0.20/0.49    inference(resolution,[],[f36,f61])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    ( ! [X2,X1] : (k1_xboole_0 != sK2 | r2_hidden(X1,X2)) ) | ~spl4_2),
% 0.20/0.49    inference(forward_demodulation,[],[f110,f108])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    ( ! [X2,X1] : (k1_xboole_0 != k4_xboole_0(sK2,X2) | r2_hidden(X1,X2)) ) | ~spl4_2),
% 0.20/0.49    inference(backward_demodulation,[],[f55,f108])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0)) ) | ~spl4_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f136,f108])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sK2 != X0 | ~r2_hidden(X1,X0)) ) | ~spl4_2),
% 0.20/0.49    inference(forward_demodulation,[],[f118,f108])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,sK2) != X0 | ~r2_hidden(X1,X0)) ) | ~spl4_2),
% 0.20/0.49    inference(backward_demodulation,[],[f51,f108])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f33,f48])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    spl4_1 | spl4_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f49,f67,f63])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    k1_xboole_0 = k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) | k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK1)),
% 0.20/0.49    inference(definition_unfolding,[],[f27,f48,f48])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    k1_xboole_0 = k2_zfmisc_1(sK1,k1_tarski(sK2)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK2),sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (6356)------------------------------
% 0.20/0.49  % (6356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (6356)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (6356)Memory used [KB]: 10746
% 0.20/0.49  % (6356)Time elapsed: 0.007 s
% 0.20/0.49  % (6356)------------------------------
% 0.20/0.49  % (6356)------------------------------
% 0.20/0.50  % (6345)Success in time 0.131 s
%------------------------------------------------------------------------------
