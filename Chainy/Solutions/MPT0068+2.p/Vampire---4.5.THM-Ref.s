%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0068+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   15 (  20 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  48 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f401,plain,(
    $false ),
    inference(subsumption_resolution,[],[f396,f230])).

fof(f230,plain,(
    ~ r2_xboole_0(k1_xboole_0,sK8) ),
    inference(cnf_transformation,[],[f179])).

fof(f179,plain,
    ( ~ r2_xboole_0(k1_xboole_0,sK8)
    & k1_xboole_0 != sK8 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f115,f178])).

fof(f178,plain,
    ( ? [X0] :
        ( ~ r2_xboole_0(k1_xboole_0,X0)
        & k1_xboole_0 != X0 )
   => ( ~ r2_xboole_0(k1_xboole_0,sK8)
      & k1_xboole_0 != sK8 ) ),
    introduced(choice_axiom,[])).

fof(f115,plain,(
    ? [X0] :
      ( ~ r2_xboole_0(k1_xboole_0,X0)
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f104])).

fof(f104,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => r2_xboole_0(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f103])).

fof(f103,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

fof(f396,plain,(
    r2_xboole_0(k1_xboole_0,sK8) ),
    inference(unit_resulting_resolution,[],[f257,f229,f241])).

fof(f241,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f182])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f229,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f179])).

fof(f257,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
%------------------------------------------------------------------------------
