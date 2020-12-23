%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0634+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:41 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   26 (  48 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :   11
%              Number of atoms          :   50 ( 102 expanded)
%              Number of equality atoms :   24 (  47 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3301,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3300,f1999])).

fof(f1999,plain,(
    v1_relat_1(sK87) ),
    inference(cnf_transformation,[],[f1578])).

fof(f1578,plain,
    ( k3_xboole_0(k1_relat_1(sK87),sK86) != k1_relat_1(k5_relat_1(k6_relat_1(sK86),sK87))
    & v1_funct_1(sK87)
    & v1_relat_1(sK87) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK86,sK87])],[f935,f1577])).

fof(f1577,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k3_xboole_0(k1_relat_1(sK87),sK86) != k1_relat_1(k5_relat_1(k6_relat_1(sK86),sK87))
      & v1_funct_1(sK87)
      & v1_relat_1(sK87) ) ),
    introduced(choice_axiom,[])).

fof(f935,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f934])).

fof(f934,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) != k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f925])).

fof(f925,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(negated_conjecture,[],[f924])).

fof(f924,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_1)).

fof(f3300,plain,(
    ~ v1_relat_1(sK87) ),
    inference(trivial_inequality_removal,[],[f3290])).

fof(f3290,plain,
    ( k1_relat_1(k7_relat_1(sK87,sK86)) != k1_relat_1(k7_relat_1(sK87,sK86))
    | ~ v1_relat_1(sK87) ),
    inference(superposition,[],[f3287,f2073])).

fof(f2073,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f985])).

fof(f985,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f883])).

fof(f883,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f3287,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1(sK86),sK87)) != k1_relat_1(k7_relat_1(sK87,sK86)) ),
    inference(subsumption_resolution,[],[f3271,f1999])).

fof(f3271,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(sK86),sK87)) != k1_relat_1(k7_relat_1(sK87,sK86))
    | ~ v1_relat_1(sK87) ),
    inference(superposition,[],[f2970,f3026])).

fof(f3026,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k6_subset_1(k1_relat_1(X1),k6_subset_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f2280,f2967])).

fof(f2967,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f2134,f2962,f2962])).

fof(f2962,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f493])).

fof(f493,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f2134,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f2280,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1116])).

fof(f1116,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f879])).

fof(f879,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f2970,plain,(
    k1_relat_1(k5_relat_1(k6_relat_1(sK86),sK87)) != k6_subset_1(k1_relat_1(sK87),k6_subset_1(k1_relat_1(sK87),sK86)) ),
    inference(definition_unfolding,[],[f2001,f2967])).

fof(f2001,plain,(
    k3_xboole_0(k1_relat_1(sK87),sK86) != k1_relat_1(k5_relat_1(k6_relat_1(sK86),sK87)) ),
    inference(cnf_transformation,[],[f1578])).
%------------------------------------------------------------------------------
