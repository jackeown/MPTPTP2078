%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0587+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:38 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   20 (  25 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  50 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2898,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2897,f1745])).

fof(f1745,plain,(
    v1_relat_1(sK68) ),
    inference(cnf_transformation,[],[f1395])).

fof(f1395,plain,
    ( k6_subset_1(k1_relat_1(sK68),sK67) != k1_relat_1(k7_relat_1(sK68,k6_subset_1(k1_relat_1(sK68),sK67)))
    & v1_relat_1(sK68) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK67,sK68])],[f853,f1394])).

fof(f1394,plain,
    ( ? [X0,X1] :
        ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
        & v1_relat_1(X1) )
   => ( k6_subset_1(k1_relat_1(sK68),sK67) != k1_relat_1(k7_relat_1(sK68,k6_subset_1(k1_relat_1(sK68),sK67)))
      & v1_relat_1(sK68) ) ),
    introduced(choice_axiom,[])).

fof(f853,plain,(
    ? [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f781])).

fof(f781,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    inference(negated_conjecture,[],[f780])).

fof(f780,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

fof(f2897,plain,(
    ~ v1_relat_1(sK68) ),
    inference(subsumption_resolution,[],[f2887,f2771])).

fof(f2771,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f2446,f1803])).

fof(f1803,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f493])).

fof(f493,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f2446,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f2887,plain,
    ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK68),sK67),k1_relat_1(sK68))
    | ~ v1_relat_1(sK68) ),
    inference(trivial_inequality_removal,[],[f2884])).

fof(f2884,plain,
    ( k6_subset_1(k1_relat_1(sK68),sK67) != k6_subset_1(k1_relat_1(sK68),sK67)
    | ~ r1_tarski(k6_subset_1(k1_relat_1(sK68),sK67),k1_relat_1(sK68))
    | ~ v1_relat_1(sK68) ),
    inference(superposition,[],[f1746,f1773])).

fof(f1773,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f882])).

fof(f882,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f881])).

fof(f881,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f839])).

fof(f839,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f1746,plain,(
    k6_subset_1(k1_relat_1(sK68),sK67) != k1_relat_1(k7_relat_1(sK68,k6_subset_1(k1_relat_1(sK68),sK67))) ),
    inference(cnf_transformation,[],[f1395])).
%------------------------------------------------------------------------------
