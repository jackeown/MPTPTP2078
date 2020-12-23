%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0499+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:33 EST 2020

% Result     : Theorem 2.08s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   21 (  40 expanded)
%              Number of leaves         :    4 (  10 expanded)
%              Depth                    :    9
%              Number of atoms          :   48 ( 112 expanded)
%              Number of equality atoms :   19 (  40 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3597,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3583,f1437])).

fof(f1437,plain,(
    sK7 != k7_relat_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f1152])).

fof(f1152,plain,
    ( sK7 != k7_relat_1(sK7,sK6)
    & r1_tarski(k1_relat_1(sK7),sK6)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f749,f1151])).

fof(f1151,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != X1
        & r1_tarski(k1_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( sK7 != k7_relat_1(sK7,sK6)
      & r1_tarski(k1_relat_1(sK7),sK6)
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f749,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != X1
      & r1_tarski(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f748])).

fof(f748,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != X1
      & r1_tarski(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f742])).

fof(f742,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k1_relat_1(X1),X0)
         => k7_relat_1(X1,X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f741])).

fof(f741,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f3583,plain,(
    sK7 = k7_relat_1(sK7,sK6) ),
    inference(superposition,[],[f2318,f2396])).

fof(f2396,plain,(
    sK7 = k5_relat_1(k6_relat_1(sK6),sK7) ),
    inference(subsumption_resolution,[],[f2377,f1435])).

fof(f1435,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f1152])).

fof(f2377,plain,
    ( sK7 = k5_relat_1(k6_relat_1(sK6),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(resolution,[],[f1436,f1726])).

fof(f1726,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f905])).

fof(f905,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f904])).

fof(f904,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f724])).

fof(f724,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f1436,plain,(
    r1_tarski(k1_relat_1(sK7),sK6) ),
    inference(cnf_transformation,[],[f1152])).

fof(f2318,plain,(
    ! [X7] : k5_relat_1(k6_relat_1(X7),sK7) = k7_relat_1(sK7,X7) ),
    inference(resolution,[],[f1435,f1599])).

fof(f1599,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f806])).

fof(f806,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f738])).

fof(f738,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
%------------------------------------------------------------------------------
