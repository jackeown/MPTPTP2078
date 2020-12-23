%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0044+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  41 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 107 expanded)
%              Number of equality atoms :   23 (  40 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f22,f33,f36])).

fof(f36,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f35])).

fof(f35,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f34,f16])).

fof(f16,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f14])).

fof(f14,plain,
    ( spl2_1
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f34,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f19,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f19,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl2_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f33,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f32])).

fof(f32,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f26,f15])).

fof(f15,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f14])).

fof(f26,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f12,f20])).

fof(f20,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f18])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f22,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f10,f18,f14])).

fof(f10,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,
    ( ( ~ r1_tarski(sK0,sK1)
      | k1_xboole_0 != k4_xboole_0(sK0,sK1) )
    & ( r1_tarski(sK0,sK1)
      | k1_xboole_0 = k4_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_tarski(X0,X1)
          | k4_xboole_0(X0,X1) != k1_xboole_0 )
        & ( r1_tarski(X0,X1)
          | k4_xboole_0(X0,X1) = k1_xboole_0 ) )
   => ( ( ~ r1_tarski(sK0,sK1)
        | k1_xboole_0 != k4_xboole_0(sK0,sK1) )
      & ( r1_tarski(sK0,sK1)
        | k1_xboole_0 = k4_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <~> r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
      <=> r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f21,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f9,f18,f14])).

fof(f9,plain,
    ( r1_tarski(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
