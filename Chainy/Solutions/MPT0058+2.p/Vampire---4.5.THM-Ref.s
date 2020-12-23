%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0058+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   39 (  49 expanded)
%              Number of leaves         :   11 (  16 expanded)
%              Depth                    :   13
%              Number of atoms          :   54 (  65 expanded)
%              Number of equality atoms :   39 (  49 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f491,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f425,f490])).

fof(f490,plain,(
    spl17_1 ),
    inference(avatar_contradiction_clause,[],[f489])).

fof(f489,plain,
    ( $false
    | spl17_1 ),
    inference(subsumption_resolution,[],[f488,f362])).

fof(f362,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f235,f217])).

fof(f217,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f235,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f488,plain,
    ( o_0_0_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl17_1 ),
    inference(forward_demodulation,[],[f487,f238])).

fof(f238,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f487,plain,
    ( o_0_0_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))
    | spl17_1 ),
    inference(forward_demodulation,[],[f486,f362])).

fof(f486,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))
    | spl17_1 ),
    inference(forward_demodulation,[],[f485,f238])).

fof(f485,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))
    | spl17_1 ),
    inference(forward_demodulation,[],[f484,f283])).

fof(f283,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f484,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)
    | spl17_1 ),
    inference(forward_demodulation,[],[f483,f242])).

fof(f242,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f483,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK0),sK0)
    | spl17_1 ),
    inference(forward_demodulation,[],[f482,f244])).

fof(f244,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f482,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),sK0)
    | spl17_1 ),
    inference(forward_demodulation,[],[f426,f238])).

fof(f426,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)),sK0)
    | spl17_1 ),
    inference(unit_resulting_resolution,[],[f424,f262])).

fof(f262,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f424,plain,
    ( sK0 != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl17_1 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl17_1
  <=> sK0 = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_1])])).

fof(f425,plain,(
    ~ spl17_1 ),
    inference(avatar_split_clause,[],[f349,f422])).

fof(f349,plain,(
    sK0 != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f214,f243])).

fof(f243,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f214,plain,(
    sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f162])).

fof(f162,plain,(
    sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f107,f161])).

fof(f161,plain,
    ( ? [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) != X0
   => sK0 != k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f107,plain,(
    ? [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) != X0 ),
    inference(ennf_transformation,[],[f92])).

fof(f92,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(negated_conjecture,[],[f91])).

fof(f91,conjecture,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
%------------------------------------------------------------------------------
