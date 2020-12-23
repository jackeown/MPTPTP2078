%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0074+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  55 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 177 expanded)
%              Number of equality atoms :   16 (  37 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f40,f48])).

fof(f48,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f44,f17])).

fof(f17,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != sK0
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X0
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
   => ( k1_xboole_0 != sK0
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X2)
          & r1_tarski(X0,X1) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f44,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f35,f15])).

fof(f15,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK0,X1)
        | ~ r1_xboole_0(X1,sK2) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_3
  <=> ! [X1] :
        ( ~ r1_tarski(sK0,X1)
        | ~ r1_xboole_0(X1,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f40,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f39])).

fof(f39,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f37,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_2 ),
    inference(resolution,[],[f31,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f31,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f36,plain,
    ( spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f24,f30,f34])).

fof(f24,plain,(
    ! [X1] :
      ( r1_tarski(sK0,k1_xboole_0)
      | ~ r1_tarski(sK0,X1)
      | ~ r1_xboole_0(X1,sK2) ) ),
    inference(resolution,[],[f22,f16])).

fof(f16,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | r1_tarski(X2,k1_xboole_0)
      | ~ r1_tarski(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f21,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

%------------------------------------------------------------------------------
