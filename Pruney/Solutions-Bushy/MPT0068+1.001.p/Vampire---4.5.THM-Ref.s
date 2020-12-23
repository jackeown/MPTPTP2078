%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0068+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:17 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   20 (  25 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  48 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f17,f22,f26])).

fof(f26,plain,
    ( spl1_1
    | spl1_2 ),
    inference(avatar_contradiction_clause,[],[f25])).

fof(f25,plain,
    ( $false
    | spl1_1
    | spl1_2 ),
    inference(subsumption_resolution,[],[f24,f8])).

fof(f8,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f24,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl1_1
    | spl1_2 ),
    inference(subsumption_resolution,[],[f23,f16])).

fof(f16,plain,
    ( k1_xboole_0 != sK0
    | spl1_1 ),
    inference(avatar_component_clause,[],[f14])).

fof(f14,plain,
    ( spl1_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f23,plain,
    ( k1_xboole_0 = sK0
    | ~ r1_tarski(k1_xboole_0,sK0)
    | spl1_2 ),
    inference(resolution,[],[f21,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f21,plain,
    ( ~ r2_xboole_0(k1_xboole_0,sK0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl1_2
  <=> r2_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f22,plain,(
    ~ spl1_2 ),
    inference(avatar_split_clause,[],[f7,f19])).

fof(f7,plain,(
    ~ r2_xboole_0(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ~ r2_xboole_0(k1_xboole_0,X0)
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => r2_xboole_0(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

fof(f17,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f6,f14])).

fof(f6,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f5])).

%------------------------------------------------------------------------------
