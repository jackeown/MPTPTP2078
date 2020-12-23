%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0215+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:17 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   53 (  77 expanded)
%              Number of leaves         :   14 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   95 ( 139 expanded)
%              Number of equality atoms :   53 (  83 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f582,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f410,f415,f435,f573,f581])).

fof(f581,plain,
    ( spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f580])).

fof(f580,plain,
    ( $false
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f579,f434])).

fof(f434,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k1_tarski(sK0))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f432])).

fof(f432,plain,
    ( spl4_4
  <=> r1_tarski(k1_tarski(sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f579,plain,
    ( r1_tarski(k1_tarski(sK1),k1_tarski(sK0))
    | ~ spl4_5 ),
    inference(superposition,[],[f381,f572])).

fof(f572,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f570])).

fof(f570,plain,
    ( spl4_5
  <=> k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f381,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f573,plain,
    ( spl4_5
    | spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f545,f412,f407,f570])).

fof(f407,plain,
    ( spl4_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f412,plain,
    ( spl4_2
  <=> k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f545,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f532,f544])).

fof(f544,plain,
    ( k1_tarski(sK0) = k2_tarski(sK0,sK1)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f543,f414])).

fof(f414,plain,
    ( k1_tarski(sK0) = k2_tarski(sK1,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f412])).

fof(f543,plain,
    ( k2_tarski(sK1,sK2) = k2_tarski(sK0,sK1)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f538,f338])).

fof(f338,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f173])).

fof(f173,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f538,plain,
    ( k2_tarski(sK1,sK2) = k2_tarski(sK1,sK0)
    | ~ spl4_2 ),
    inference(superposition,[],[f463,f337])).

fof(f337,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f255])).

fof(f255,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f463,plain,
    ( ! [X0] : k2_tarski(X0,sK0) = k1_enumset1(X0,sK1,sK2)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f454,f336])).

fof(f336,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f226])).

fof(f226,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f454,plain,
    ( ! [X0] : k1_enumset1(X0,sK1,sK2) = k2_xboole_0(k1_tarski(X0),k1_tarski(sK0))
    | ~ spl4_2 ),
    inference(superposition,[],[f334,f414])).

fof(f334,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f227])).

fof(f227,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f532,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK0))
    | spl4_1 ),
    inference(forward_demodulation,[],[f531,f464])).

fof(f464,plain,(
    ! [X2,X1] : k2_tarski(X2,X1) = k1_enumset1(X2,X1,X1) ),
    inference(forward_demodulation,[],[f455,f336])).

fof(f455,plain,(
    ! [X2,X1] : k2_xboole_0(k1_tarski(X2),k1_tarski(X1)) = k1_enumset1(X2,X1,X1) ),
    inference(superposition,[],[f334,f339])).

fof(f339,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f531,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_enumset1(sK0,sK1,sK1),k1_tarski(sK0))
    | spl4_1 ),
    inference(forward_demodulation,[],[f522,f339])).

fof(f522,plain,
    ( k4_xboole_0(k1_enumset1(sK0,sK1,sK1),k1_tarski(sK0)) = k2_tarski(sK1,sK1)
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f409,f409,f331])).

fof(f331,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f298])).

fof(f298,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f224])).

fof(f224,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_enumset1)).

fof(f409,plain,
    ( sK0 != sK1
    | spl4_1 ),
    inference(avatar_component_clause,[],[f407])).

fof(f435,plain,
    ( ~ spl4_4
    | spl4_1 ),
    inference(avatar_split_clause,[],[f422,f407,f432])).

fof(f422,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k1_tarski(sK0))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f409,f342])).

fof(f342,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f299])).

fof(f299,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f293])).

fof(f293,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f415,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f327,f412])).

fof(f327,plain,(
    k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f322])).

fof(f322,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f297,f321])).

fof(f321,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & k1_tarski(X0) = k2_tarski(X1,X2) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f297,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f295])).

fof(f295,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f294])).

fof(f294,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).

fof(f410,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f328,f407])).

fof(f328,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f322])).
%------------------------------------------------------------------------------
