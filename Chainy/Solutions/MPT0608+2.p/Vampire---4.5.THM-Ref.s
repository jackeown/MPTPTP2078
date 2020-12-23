%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0608+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:40 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   22 (  39 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  76 expanded)
%              Number of equality atoms :   21 (  39 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1666,plain,(
    $false ),
    inference(subsumption_resolution,[],[f974,f1658])).

fof(f1658,plain,(
    ! [X0] : k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) ),
    inference(backward_demodulation,[],[f1264,f1646])).

fof(f1646,plain,(
    ! [X1] : k6_subset_1(sK1,k7_relat_1(sK1,X1)) = k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X1)) ),
    inference(superposition,[],[f1314,f1071])).

fof(f1071,plain,(
    sK1 = k7_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(resolution,[],[f1015,f973])).

fof(f973,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f959])).

fof(f959,plain,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f883,f958])).

fof(f958,plain,
    ( ? [X0,X1] :
        ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f883,plain,(
    ? [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f817])).

fof(f817,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f816])).

fof(f816,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

fof(f1015,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f927])).

fof(f927,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f880])).

fof(f880,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f1314,plain,(
    ! [X0,X1] : k7_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)) ),
    inference(resolution,[],[f1021,f973])).

fof(f1021,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f933])).

fof(f933,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f713])).

fof(f713,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

fof(f1264,plain,(
    ! [X0] : k6_subset_1(k1_relat_1(sK1),X0) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0))) ),
    inference(resolution,[],[f1023,f973])).

fof(f1023,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f935])).

fof(f935,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f793])).

fof(f793,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).

fof(f974,plain,(
    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f959])).
%------------------------------------------------------------------------------
