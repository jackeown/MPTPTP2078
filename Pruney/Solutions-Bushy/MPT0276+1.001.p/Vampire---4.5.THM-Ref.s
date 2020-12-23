%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0276+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:40 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   52 (  88 expanded)
%              Number of leaves         :   11 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :  158 ( 301 expanded)
%              Number of equality atoms :   60 ( 147 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f319,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f125,f314,f316,f317,f318])).

fof(f318,plain,
    ( spl4_6
    | ~ spl4_5
    | spl4_7 ),
    inference(avatar_split_clause,[],[f127,f117,f85,f89])).

fof(f89,plain,
    ( spl4_6
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f85,plain,
    ( spl4_5
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f117,plain,
    ( spl4_7
  <=> sP0(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f127,plain,
    ( ~ r2_hidden(sK1,sK3)
    | r2_hidden(sK2,sK3)
    | spl4_7 ),
    inference(resolution,[],[f119,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( X0 != X1
          & ~ r2_hidden(X0,X2) )
        | r2_hidden(X1,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X0,X2) )
          & ~ r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f119,plain,
    ( ~ sP0(sK1,sK2,sK3)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f317,plain,
    ( ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f148,f89,f85])).

fof(f148,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f137])).

fof(f137,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK1,sK3) ),
    inference(superposition,[],[f20,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f20,plain,(
    k1_xboole_0 != k4_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k2_tarski(sK1,sK2) != k4_xboole_0(k2_tarski(sK1,sK2),sK3)
    & k4_xboole_0(k2_tarski(sK1,sK2),sK3) != k1_tarski(sK2)
    & k4_xboole_0(k2_tarski(sK1,sK2),sK3) != k1_tarski(sK1)
    & k1_xboole_0 != k4_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
   => ( k2_tarski(sK1,sK2) != k4_xboole_0(k2_tarski(sK1,sK2),sK3)
      & k4_xboole_0(k2_tarski(sK1,sK2),sK3) != k1_tarski(sK2)
      & k4_xboole_0(k2_tarski(sK1,sK2),sK3) != k1_tarski(sK1)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(sK1,sK2),sK3) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_zfmisc_1)).

fof(f316,plain,
    ( spl4_5
    | ~ spl4_6
    | spl4_1 ),
    inference(avatar_split_clause,[],[f207,f60,f89,f85])).

fof(f60,plain,
    ( spl4_1
  <=> sP0(sK2,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f207,plain,
    ( ~ r2_hidden(sK2,sK3)
    | r2_hidden(sK1,sK3)
    | spl4_1 ),
    inference(resolution,[],[f30,f62])).

fof(f62,plain,
    ( ~ sP0(sK2,sK1,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f314,plain,
    ( spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f288,f89,f85])).

fof(f288,plain,
    ( r2_hidden(sK2,sK3)
    | r2_hidden(sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f273])).

fof(f273,plain,
    ( k2_tarski(sK1,sK2) != k2_tarski(sK1,sK2)
    | r2_hidden(sK2,sK3)
    | r2_hidden(sK1,sK3) ),
    inference(superposition,[],[f23,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f23,plain,(
    k2_tarski(sK1,sK2) != k4_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f125,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f115,f117])).

fof(f115,plain,(
    ~ sP0(sK1,sK2,sK3) ),
    inference(trivial_inequality_removal,[],[f105])).

fof(f105,plain,
    ( k1_tarski(sK2) != k1_tarski(sK2)
    | ~ sP0(sK1,sK2,sK3) ),
    inference(superposition,[],[f22,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X1,X0),X2)
      | ~ sP0(X1,X0,X2) ) ),
    inference(superposition,[],[f33,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
      | ~ sP0(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f8])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f22,plain,(
    k4_xboole_0(k2_tarski(sK1,sK2),sK3) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f73,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f58,f60])).

fof(f58,plain,(
    ~ sP0(sK2,sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f53])).

fof(f53,plain,
    ( k1_tarski(sK1) != k1_tarski(sK1)
    | ~ sP0(sK2,sK1,sK3) ),
    inference(superposition,[],[f21,f33])).

fof(f21,plain,(
    k4_xboole_0(k2_tarski(sK1,sK2),sK3) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
