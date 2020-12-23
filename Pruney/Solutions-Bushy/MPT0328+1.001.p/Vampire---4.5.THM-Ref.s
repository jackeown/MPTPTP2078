%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0328+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:45 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   23 (  30 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :   40 (  54 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f15,f20,f26,f29])).

fof(f29,plain,
    ( spl2_2
    | spl2_3 ),
    inference(avatar_contradiction_clause,[],[f28])).

fof(f28,plain,
    ( $false
    | spl2_2
    | spl2_3 ),
    inference(subsumption_resolution,[],[f27,f25])).

fof(f25,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(sK0))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl2_3
  <=> sK1 = k4_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f27,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(sK0))
    | spl2_2 ),
    inference(resolution,[],[f9,f19])).

fof(f19,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f17])).

fof(f17,plain,
    ( spl2_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f26,plain,
    ( ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f21,f12,f23])).

fof(f12,plain,
    ( spl2_1
  <=> sK1 = k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f21,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(sK0))
    | spl2_1 ),
    inference(superposition,[],[f14,f8])).

fof(f8,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f14,plain,
    ( sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f12])).

fof(f20,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f6,f17])).

fof(f6,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
       => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).

fof(f15,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f7,f12])).

fof(f7,plain,(
    sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f5])).

%------------------------------------------------------------------------------
