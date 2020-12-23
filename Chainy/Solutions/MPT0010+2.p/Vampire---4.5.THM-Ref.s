%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0010+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   23 (  30 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  69 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f111,f175])).

fof(f175,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f150,f86])).

fof(f86,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f150,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ spl7_1
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f110,f105,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f105,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl7_1
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f110,plain,
    ( k1_xboole_0 != sK0
    | spl7_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f111,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f78,f108])).

fof(f78,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( k1_xboole_0 != sK0
    & r1_tarski(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f45,f56])).

fof(f56,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_tarski(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK0
      & r1_tarski(sK0,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,negated_conjecture,(
    ~ ! [X0] :
        ( r1_tarski(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f40])).

fof(f40,conjecture,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f106,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f77,f103])).

fof(f77,plain,(
    r1_tarski(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
