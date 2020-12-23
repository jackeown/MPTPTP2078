%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0525+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:35 EST 2020

% Result     : Theorem 2.31s
% Output     : Refutation 2.31s
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
fof(f4360,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4346,f1496])).

fof(f1496,plain,(
    sK7 != k8_relat_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f1212])).

fof(f1212,plain,
    ( sK7 != k8_relat_1(sK6,sK7)
    & r1_tarski(k2_relat_1(sK7),sK6)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f779,f1211])).

fof(f1211,plain,
    ( ? [X0,X1] :
        ( k8_relat_1(X0,X1) != X1
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( sK7 != k8_relat_1(sK6,sK7)
      & r1_tarski(k2_relat_1(sK7),sK6)
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f779,plain,(
    ? [X0,X1] :
      ( k8_relat_1(X0,X1) != X1
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f778])).

fof(f778,plain,(
    ? [X0,X1] :
      ( k8_relat_1(X0,X1) != X1
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f702])).

fof(f702,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k2_relat_1(X1),X0)
         => k8_relat_1(X0,X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f701])).

fof(f701,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f4346,plain,(
    sK7 = k8_relat_1(sK6,sK7) ),
    inference(superposition,[],[f2400,f2506])).

fof(f2506,plain,(
    sK7 = k5_relat_1(sK7,k6_relat_1(sK6)) ),
    inference(subsumption_resolution,[],[f2482,f1494])).

fof(f1494,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f1212])).

fof(f2482,plain,
    ( sK7 = k5_relat_1(sK7,k6_relat_1(sK6))
    | ~ v1_relat_1(sK7) ),
    inference(resolution,[],[f1495,f1736])).

fof(f1736,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f927])).

fof(f927,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f926])).

fof(f926,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f755])).

fof(f755,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f1495,plain,(
    r1_tarski(k2_relat_1(sK7),sK6) ),
    inference(cnf_transformation,[],[f1212])).

fof(f2400,plain,(
    ! [X11] : k8_relat_1(X11,sK7) = k5_relat_1(sK7,k6_relat_1(X11)) ),
    inference(resolution,[],[f1494,f1609])).

fof(f1609,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f827])).

fof(f827,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f699])).

fof(f699,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
%------------------------------------------------------------------------------
