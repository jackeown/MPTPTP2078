%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0290+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:22 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   34 (  43 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :   60 (  76 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1160,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f517,f913,f948,f1147])).

fof(f1147,plain,(
    spl8_14 ),
    inference(avatar_contradiction_clause,[],[f1146])).

fof(f1146,plain,
    ( $false
    | spl8_14 ),
    inference(subsumption_resolution,[],[f1140,f507])).

fof(f507,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1140,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | spl8_14 ),
    inference(resolution,[],[f947,f465])).

fof(f465,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f408])).

fof(f408,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f386])).

fof(f386,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f947,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0))
    | spl8_14 ),
    inference(avatar_component_clause,[],[f946])).

fof(f946,plain,
    ( spl8_14
  <=> r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f948,plain,
    ( ~ spl8_14
    | ~ spl8_6
    | spl8_1 ),
    inference(avatar_split_clause,[],[f932,f515,f861,f946])).

fof(f861,plain,
    ( spl8_6
  <=> r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f515,plain,
    ( spl8_1
  <=> r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f932,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1))
    | ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK0))
    | spl8_1 ),
    inference(resolution,[],[f478,f516])).

fof(f516,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1)))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f515])).

fof(f478,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f416])).

fof(f416,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f415])).

fof(f415,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f75])).

fof(f75,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f913,plain,(
    spl8_6 ),
    inference(avatar_contradiction_clause,[],[f912])).

fof(f912,plain,
    ( $false
    | spl8_6 ),
    inference(subsumption_resolution,[],[f906,f538])).

fof(f538,plain,(
    ! [X6,X5] : r1_tarski(k3_xboole_0(X6,X5),X5) ),
    inference(superposition,[],[f507,f506])).

fof(f506,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f906,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | spl8_6 ),
    inference(resolution,[],[f862,f465])).

fof(f862,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_tarski(sK1))
    | spl8_6 ),
    inference(avatar_component_clause,[],[f861])).

fof(f517,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f440,f515])).

fof(f440,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(cnf_transformation,[],[f425])).

fof(f425,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f392,f424])).

fof(f424,plain,
    ( ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1)))
   => ~ r1_tarski(k3_tarski(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_tarski(sK0),k3_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f392,plain,(
    ? [X0,X1] : ~ r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(ennf_transformation,[],[f389])).

fof(f389,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    inference(negated_conjecture,[],[f388])).

fof(f388,conjecture,(
    ! [X0,X1] : r1_tarski(k3_tarski(k3_xboole_0(X0,X1)),k3_xboole_0(k3_tarski(X0),k3_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_zfmisc_1)).
%------------------------------------------------------------------------------
