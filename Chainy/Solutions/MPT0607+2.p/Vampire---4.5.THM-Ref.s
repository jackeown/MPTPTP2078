%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0607+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:40 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   21 (  40 expanded)
%              Number of leaves         :    4 (  10 expanded)
%              Depth                    :    9
%              Number of atoms          :   48 ( 112 expanded)
%              Number of equality atoms :   19 (  40 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1775,plain,(
    $false ),
    inference(subsumption_resolution,[],[f978,f1754])).

fof(f1754,plain,(
    ! [X6] : k7_relat_1(sK2,k6_subset_1(sK0,X6)) = k6_subset_1(sK2,k7_relat_1(sK2,X6)) ),
    inference(superposition,[],[f1343,f1250])).

fof(f1250,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(resolution,[],[f1155,f977])).

fof(f977,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f960])).

fof(f960,plain,
    ( k7_relat_1(sK2,k6_subset_1(sK0,sK1)) != k6_subset_1(sK2,k7_relat_1(sK2,sK1))
    & r1_tarski(k1_relat_1(sK2),sK0)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f883,f959])).

fof(f959,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(X2,k6_subset_1(X0,X1)) != k6_subset_1(X2,k7_relat_1(X2,X1))
        & r1_tarski(k1_relat_1(X2),X0)
        & v1_relat_1(X2) )
   => ( k7_relat_1(sK2,k6_subset_1(sK0,sK1)) != k6_subset_1(sK2,k7_relat_1(sK2,sK1))
      & r1_tarski(k1_relat_1(sK2),sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f883,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) != k6_subset_1(X2,k7_relat_1(X2,X1))
      & r1_tarski(k1_relat_1(X2),X0)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f882])).

fof(f882,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) != k6_subset_1(X2,k7_relat_1(X2,X1))
      & r1_tarski(k1_relat_1(X2),X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f816])).

fof(f816,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(k1_relat_1(X2),X0)
         => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(X2,k7_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f815])).

fof(f815,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(X2,k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

fof(f1155,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | sK2 = k7_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f998,f976])).

fof(f976,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f960])).

fof(f998,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f908])).

fof(f908,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f907])).

fof(f907,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f878])).

fof(f878,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f1343,plain,(
    ! [X0,X1] : k7_relat_1(sK2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1)) ),
    inference(resolution,[],[f1024,f976])).

fof(f1024,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f931])).

fof(f931,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f713])).

fof(f713,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

fof(f978,plain,(
    k7_relat_1(sK2,k6_subset_1(sK0,sK1)) != k6_subset_1(sK2,k7_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f960])).
%------------------------------------------------------------------------------
