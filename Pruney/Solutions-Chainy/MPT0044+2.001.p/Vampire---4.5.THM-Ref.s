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
% DateTime   : Thu Dec  3 12:29:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 138 expanded)
%              Number of leaves         :   16 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  269 ( 562 expanded)
%              Number of equality atoms :   32 (  61 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f448,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f62,f404,f426,f429,f446])).

fof(f446,plain,
    ( spl7_2
    | ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | spl7_2
    | ~ spl7_15 ),
    inference(resolution,[],[f440,f60])).

fof(f60,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl7_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f440,plain,
    ( r1_tarski(sK1,sK2)
    | spl7_2
    | ~ spl7_15 ),
    inference(resolution,[],[f435,f405])).

fof(f405,plain,
    ( r2_hidden(sK5(sK1,sK2),sK1)
    | spl7_2 ),
    inference(resolution,[],[f60,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f435,plain,
    ( ! [X5] :
        ( ~ r2_hidden(sK5(X5,sK2),sK1)
        | r1_tarski(X5,sK2) )
    | ~ spl7_15 ),
    inference(resolution,[],[f421,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f421,plain,
    ( ! [X5] :
        ( r2_hidden(X5,sK2)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f420])).

fof(f420,plain,
    ( spl7_15
  <=> ! [X5] :
        ( r2_hidden(X5,sK2)
        | ~ r2_hidden(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f429,plain,(
    spl7_16 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | spl7_16 ),
    inference(resolution,[],[f425,f36])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f425,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl7_16 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl7_16
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f426,plain,
    ( spl7_15
    | ~ spl7_16
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f418,f54,f423,f420])).

fof(f54,plain,
    ( spl7_1
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f418,plain,
    ( ! [X5] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | r2_hidden(X5,sK2)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl7_1 ),
    inference(superposition,[],[f235,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f235,plain,(
    ! [X14,X15,X16] :
      ( ~ v1_xboole_0(k4_xboole_0(X15,X16))
      | r2_hidden(X14,X16)
      | ~ r2_hidden(X14,X15) ) ),
    inference(resolution,[],[f126,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X2,X1))
      | ~ r2_hidden(X0,X2)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f46,f52])).

fof(f52,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f13])).

fof(f13,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(sK6(X0,X1,X2),X1) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
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
    inference(nnf_transformation,[],[f13])).

fof(f404,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f403])).

fof(f403,plain,
    ( $false
    | spl7_1
    | ~ spl7_2 ),
    inference(trivial_inequality_removal,[],[f391])).

fof(f391,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl7_1
    | ~ spl7_2 ),
    inference(superposition,[],[f56,f389])).

fof(f389,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f387])).

fof(f387,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl7_2 ),
    inference(resolution,[],[f87,f259])).

fof(f259,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(k4_xboole_0(sK1,X0)),sK2)
        | k1_xboole_0 = k4_xboole_0(sK1,X0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f257,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k4_xboole_0(X0,X1)),X0)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f83,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f44,f52])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f257,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK2) )
    | ~ spl7_2 ),
    inference(resolution,[],[f59,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(k4_xboole_0(X0,X1)),X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f86,f39])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f45,f52])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f62,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f34,f58,f54])).

fof(f34,plain,
    ( r1_tarski(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ~ r1_tarski(sK1,sK2)
      | k1_xboole_0 != k4_xboole_0(sK1,sK2) )
    & ( r1_tarski(sK1,sK2)
      | k1_xboole_0 = k4_xboole_0(sK1,sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_tarski(X0,X1)
          | k4_xboole_0(X0,X1) != k1_xboole_0 )
        & ( r1_tarski(X0,X1)
          | k4_xboole_0(X0,X1) = k1_xboole_0 ) )
   => ( ( ~ r1_tarski(sK1,sK2)
        | k1_xboole_0 != k4_xboole_0(sK1,sK2) )
      & ( r1_tarski(sK1,sK2)
        | k1_xboole_0 = k4_xboole_0(sK1,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <~> r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
      <=> r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f61,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f35,f58,f54])).

fof(f35,plain,
    ( ~ r1_tarski(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:30:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (20267)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.49  % (20251)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (20251)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f448,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f61,f62,f404,f426,f429,f446])).
% 0.21/0.51  fof(f446,plain,(
% 0.21/0.51    spl7_2 | ~spl7_15),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f442])).
% 0.21/0.51  fof(f442,plain,(
% 0.21/0.51    $false | (spl7_2 | ~spl7_15)),
% 0.21/0.51    inference(resolution,[],[f440,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ~r1_tarski(sK1,sK2) | spl7_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    spl7_2 <=> r1_tarski(sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.51  fof(f440,plain,(
% 0.21/0.51    r1_tarski(sK1,sK2) | (spl7_2 | ~spl7_15)),
% 0.21/0.51    inference(resolution,[],[f435,f405])).
% 0.21/0.51  fof(f405,plain,(
% 0.21/0.51    r2_hidden(sK5(sK1,sK2),sK1) | spl7_2),
% 0.21/0.51    inference(resolution,[],[f60,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.51  fof(f435,plain,(
% 0.21/0.51    ( ! [X5] : (~r2_hidden(sK5(X5,sK2),sK1) | r1_tarski(X5,sK2)) ) | ~spl7_15),
% 0.21/0.51    inference(resolution,[],[f421,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f421,plain,(
% 0.21/0.51    ( ! [X5] : (r2_hidden(X5,sK2) | ~r2_hidden(X5,sK1)) ) | ~spl7_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f420])).
% 0.21/0.51  fof(f420,plain,(
% 0.21/0.51    spl7_15 <=> ! [X5] : (r2_hidden(X5,sK2) | ~r2_hidden(X5,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.51  fof(f429,plain,(
% 0.21/0.51    spl7_16),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f427])).
% 0.21/0.51  fof(f427,plain,(
% 0.21/0.51    $false | spl7_16),
% 0.21/0.51    inference(resolution,[],[f425,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.51  fof(f425,plain,(
% 0.21/0.51    ~v1_xboole_0(k1_xboole_0) | spl7_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f423])).
% 0.21/0.51  fof(f423,plain,(
% 0.21/0.51    spl7_16 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.51  fof(f426,plain,(
% 0.21/0.51    spl7_15 | ~spl7_16 | ~spl7_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f418,f54,f423,f420])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    spl7_1 <=> k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.51  fof(f418,plain,(
% 0.21/0.51    ( ! [X5] : (~v1_xboole_0(k1_xboole_0) | r2_hidden(X5,sK2) | ~r2_hidden(X5,sK1)) ) | ~spl7_1),
% 0.21/0.51    inference(superposition,[],[f235,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK1,sK2) | ~spl7_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f54])).
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    ( ! [X14,X15,X16] : (~v1_xboole_0(k4_xboole_0(X15,X16)) | r2_hidden(X14,X16) | ~r2_hidden(X14,X15)) )),
% 0.21/0.51    inference(resolution,[],[f126,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.51    inference(rectify,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X2,X1)) | ~r2_hidden(X0,X2) | r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(resolution,[],[f46,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.21/0.51    inference(definition_folding,[],[f3,f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1) | r2_hidden(X4,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f30,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.51    inference(rectify,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.51    inference(nnf_transformation,[],[f13])).
% 0.21/0.51  fof(f404,plain,(
% 0.21/0.51    spl7_1 | ~spl7_2),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f403])).
% 0.21/0.51  fof(f403,plain,(
% 0.21/0.51    $false | (spl7_1 | ~spl7_2)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f391])).
% 0.21/0.51  fof(f391,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | (spl7_1 | ~spl7_2)),
% 0.21/0.51    inference(superposition,[],[f56,f389])).
% 0.21/0.51  fof(f389,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK1,sK2) | ~spl7_2),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f387])).
% 0.21/0.51  fof(f387,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK1,sK2) | ~spl7_2),
% 0.21/0.51    inference(resolution,[],[f87,f259])).
% 0.21/0.51  fof(f259,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK4(k4_xboole_0(sK1,X0)),sK2) | k1_xboole_0 = k4_xboole_0(sK1,X0)) ) | ~spl7_2),
% 0.21/0.51    inference(resolution,[],[f257,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK4(k4_xboole_0(X0,X1)),X0) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.51    inference(resolution,[],[f83,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(resolution,[],[f44,f52])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | r2_hidden(X4,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f257,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK2)) ) | ~spl7_2),
% 0.21/0.51    inference(resolution,[],[f59,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    r1_tarski(sK1,sK2) | ~spl7_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f58])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK4(k4_xboole_0(X0,X1)),X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.51    inference(resolution,[],[f86,f39])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | ~r2_hidden(X0,X2)) )),
% 0.21/0.51    inference(resolution,[],[f45,f52])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~r2_hidden(X4,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    k1_xboole_0 != k4_xboole_0(sK1,sK2) | spl7_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f54])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl7_1 | spl7_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f58,f54])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    r1_tarski(sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    (~r1_tarski(sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK1,sK2)) & (r1_tarski(sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK1,sK2))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f15,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0,X1] : ((~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0)) => ((~r1_tarski(sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK1,sK2)) & (r1_tarski(sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK1,sK2)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0,X1] : ((~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0))),
% 0.21/0.51    inference(nnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <~> r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.51    inference(negated_conjecture,[],[f7])).
% 0.21/0.51  fof(f7,conjecture,(
% 0.21/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ~spl7_1 | ~spl7_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f35,f58,f54])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ~r1_tarski(sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (20251)------------------------------
% 0.21/0.51  % (20251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (20251)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (20251)Memory used [KB]: 6396
% 0.21/0.51  % (20251)Time elapsed: 0.093 s
% 0.21/0.51  % (20251)------------------------------
% 0.21/0.51  % (20251)------------------------------
% 0.21/0.51  % (20238)Success in time 0.143 s
%------------------------------------------------------------------------------
