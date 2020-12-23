%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0769+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:48 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   17 (  28 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  55 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2175,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2169,f1535])).

fof(f1535,plain,(
    ! [X10] : k2_wellord1(sK1,X10) = k7_relat_1(k8_relat_1(X10,sK1),X10) ),
    inference(resolution,[],[f1406,f1294])).

fof(f1294,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1269])).

fof(f1269,plain,
    ( k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1157,f1268])).

fof(f1268,plain,
    ( ? [X0,X1] :
        ( k2_wellord1(X1,X0) != k8_relat_1(X0,k7_relat_1(X1,X0))
        & v1_relat_1(X1) )
   => ( k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1157,plain,(
    ? [X0,X1] :
      ( k2_wellord1(X1,X0) != k8_relat_1(X0,k7_relat_1(X1,X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1151])).

fof(f1151,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    inference(negated_conjecture,[],[f1150])).

fof(f1150,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

fof(f1406,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1265])).

fof(f1265,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1149])).

fof(f1149,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).

fof(f2169,plain,(
    k2_wellord1(sK1,sK0) != k7_relat_1(k8_relat_1(sK0,sK1),sK0) ),
    inference(superposition,[],[f1295,f1634])).

fof(f1634,plain,(
    ! [X14,X15] : k7_relat_1(k8_relat_1(X14,sK1),X15) = k8_relat_1(X14,k7_relat_1(sK1,X15)) ),
    inference(resolution,[],[f1313,f1294])).

fof(f1313,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f1179])).

fof(f1179,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f744])).

fof(f744,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(f1295,plain,(
    k2_wellord1(sK1,sK0) != k8_relat_1(sK0,k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f1269])).
%------------------------------------------------------------------------------
