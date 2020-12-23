%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0483+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   18 (  23 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  58 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2440,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2114,f1151])).

fof(f1151,plain,(
    sK0 != k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) ),
    inference(cnf_transformation,[],[f964])).

fof(f964,plain,
    ( sK0 != k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f729,f963])).

fof(f963,plain,
    ( ? [X0] :
        ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) != X0
        & v1_relat_1(X0) )
   => ( sK0 != k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f729,plain,(
    ? [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f723])).

fof(f723,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(negated_conjecture,[],[f722])).

fof(f722,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f2114,plain,(
    sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f1673,f1150,f1190])).

fof(f1190,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f761])).

fof(f761,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f760])).

fof(f760,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f721])).

fof(f721,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f1150,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f964])).

fof(f1673,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1241])).

fof(f1241,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1004])).

fof(f1004,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1003])).

fof(f1003,plain,(
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
%------------------------------------------------------------------------------
