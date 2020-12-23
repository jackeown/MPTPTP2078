%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0605+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:39 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   22 (  41 expanded)
%              Number of leaves         :    4 (  10 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 ( 123 expanded)
%              Number of equality atoms :   16 (  37 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1214,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1212,f948])).

fof(f948,plain,(
    sK1 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f936])).

fof(f936,plain,
    ( sK1 != k7_relat_1(sK1,sK0)
    & v4_relat_1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f881,f935])).

fof(f935,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != X1
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( sK1 != k7_relat_1(sK1,sK0)
      & v4_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f881,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != X1
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f880])).

fof(f880,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != X1
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f813])).

fof(f813,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v4_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => k7_relat_1(X1,X0) = X1 ) ),
    inference(negated_conjecture,[],[f812])).

fof(f812,conjecture,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f1212,plain,(
    sK1 = k7_relat_1(sK1,sK0) ),
    inference(resolution,[],[f1211,f947])).

fof(f947,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f936])).

fof(f1211,plain,(
    ! [X0] :
      ( ~ v4_relat_1(sK1,X0)
      | sK1 = k7_relat_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f1210,f946])).

fof(f946,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f936])).

fof(f1210,plain,(
    ! [X0] :
      ( sK1 = k7_relat_1(sK1,X0)
      | ~ v4_relat_1(sK1,X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f1051,f999])).

fof(f999,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f945])).

fof(f945,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f934])).

fof(f934,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f650])).

fof(f650,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f1051,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),X0)
      | sK1 = k7_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f972,f946])).

fof(f972,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f911])).

fof(f911,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f910])).

fof(f910,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f876])).

fof(f876,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
%------------------------------------------------------------------------------
