%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0680+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:44 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   27 (  61 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 ( 196 expanded)
%              Number of equality atoms :   22 (  60 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3897,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3896,f2279])).

fof(f2279,plain,(
    v1_relat_1(sK109) ),
    inference(cnf_transformation,[],[f1784])).

fof(f1784,plain,
    ( ~ v2_funct_1(sK109)
    & ! [X1,X2] : k9_relat_1(sK109,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK109,X1),k9_relat_1(sK109,X2))
    & v1_funct_1(sK109)
    & v1_relat_1(sK109) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK109])],[f1000,f1783])).

fof(f1783,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(X0)
        & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(sK109)
      & ! [X2,X1] : k9_relat_1(sK109,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK109,X1),k9_relat_1(sK109,X2))
      & v1_funct_1(sK109)
      & v1_relat_1(sK109) ) ),
    introduced(choice_axiom,[])).

fof(f1000,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f999])).

fof(f999,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f933])).

fof(f933,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f932])).

fof(f932,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1,X2] : k9_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_funct_1)).

fof(f3896,plain,(
    ~ v1_relat_1(sK109) ),
    inference(subsumption_resolution,[],[f3895,f2280])).

fof(f2280,plain,(
    v1_funct_1(sK109) ),
    inference(cnf_transformation,[],[f1784])).

fof(f3895,plain,
    ( ~ v1_funct_1(sK109)
    | ~ v1_relat_1(sK109) ),
    inference(subsumption_resolution,[],[f3894,f2282])).

fof(f2282,plain,(
    ~ v2_funct_1(sK109) ),
    inference(cnf_transformation,[],[f1784])).

fof(f3894,plain,
    ( v2_funct_1(sK109)
    | ~ v1_funct_1(sK109)
    | ~ v1_relat_1(sK109) ),
    inference(subsumption_resolution,[],[f3753,f2281])).

fof(f2281,plain,(
    ! [X2,X1] : k9_relat_1(sK109,k6_subset_1(X1,X2)) = k6_subset_1(k9_relat_1(sK109,X1),k9_relat_1(sK109,X2)) ),
    inference(cnf_transformation,[],[f1784])).

fof(f3753,plain,
    ( k9_relat_1(sK109,k6_subset_1(sK115(sK109),k6_subset_1(sK115(sK109),sK116(sK109)))) != k6_subset_1(k9_relat_1(sK109,sK115(sK109)),k9_relat_1(sK109,k6_subset_1(sK115(sK109),sK116(sK109))))
    | v2_funct_1(sK109)
    | ~ v1_funct_1(sK109)
    | ~ v1_relat_1(sK109) ),
    inference(superposition,[],[f3415,f2281])).

fof(f3415,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k6_subset_1(sK115(X0),k6_subset_1(sK115(X0),sK116(X0)))) != k6_subset_1(k9_relat_1(X0,sK115(X0)),k6_subset_1(k9_relat_1(X0,sK115(X0)),k9_relat_1(X0,sK116(X0))))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f2319,f3411,f3411])).

fof(f3411,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f2485,f2387,f2387])).

fof(f2387,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f493])).

fof(f493,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f2485,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f2319,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k9_relat_1(X0,k3_xboole_0(sK115(X0),sK116(X0))) != k3_xboole_0(k9_relat_1(X0,sK115(X0)),k9_relat_1(X0,sK116(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1799])).

fof(f1799,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k9_relat_1(X0,k3_xboole_0(sK115(X0),sK116(X0))) != k3_xboole_0(k9_relat_1(X0,sK115(X0)),k9_relat_1(X0,sK116(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK115,sK116])],[f1026,f1798])).

fof(f1798,plain,(
    ! [X0] :
      ( ? [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
     => k9_relat_1(X0,k3_xboole_0(sK115(X0),sK116(X0))) != k3_xboole_0(k9_relat_1(X0,sK115(X0)),k9_relat_1(X0,sK116(X0))) ) ),
    introduced(choice_axiom,[])).

fof(f1026,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ? [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1025])).

fof(f1025,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ? [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f930])).

fof(f930,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1,X2] : k9_relat_1(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_funct_1)).
%------------------------------------------------------------------------------
