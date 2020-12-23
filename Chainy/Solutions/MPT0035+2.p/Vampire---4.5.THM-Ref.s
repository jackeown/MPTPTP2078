%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0035+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  35 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 (  68 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f200,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f141,f145,f193,f199])).

fof(f199,plain,
    ( spl4_1
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f196,f140])).

fof(f140,plain,
    ( sK0 != k3_xboole_0(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl4_1
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f196,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_3 ),
    inference(superposition,[],[f118,f192])).

fof(f192,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl4_3
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f118,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f53])).

fof(f53,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f193,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f184,f143,f191])).

fof(f143,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f184,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f134,f144])).

fof(f144,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f143])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f145,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f104,f143])).

fof(f104,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,
    ( sK0 != k3_xboole_0(sK0,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f75,f96])).

fof(f96,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(X0,X1) != X0
        & r1_tarski(X0,X1) )
   => ( sK0 != k3_xboole_0(sK0,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(X0,X1) != X0
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f61])).

fof(f61,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => k3_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f60])).

fof(f60,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f141,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f105,f139])).

fof(f105,plain,(
    sK0 != k3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f97])).
%------------------------------------------------------------------------------
