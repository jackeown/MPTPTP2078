%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0612+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:40 EST 2020

% Result     : Theorem 2.02s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   34 (  57 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :   11
%              Number of atoms          :   67 ( 135 expanded)
%              Number of equality atoms :   21 (  46 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2575,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2574,f2359])).

fof(f2359,plain,(
    ! [X60] : r1_xboole_0(sK0,k4_xboole_0(X60,sK1)) ),
    inference(resolution,[],[f1396,f1726])).

fof(f1726,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1163])).

fof(f1163,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f155])).

fof(f155,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f1396,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f1263])).

fof(f1263,plain,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f891,f1262])).

fof(f1262,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f891,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f890])).

fof(f890,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f821])).

fof(f821,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    inference(negated_conjecture,[],[f820])).

fof(f820,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

fof(f2574,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(forward_demodulation,[],[f2573,f2210])).

fof(f2210,plain,(
    ! [X12] : k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X12))) = k4_xboole_0(k1_relat_1(sK2),X12) ),
    inference(forward_demodulation,[],[f2209,f1406])).

fof(f1406,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f493])).

fof(f493,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f2209,plain,(
    ! [X12] : k6_subset_1(k1_relat_1(sK2),X12) = k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X12))) ),
    inference(forward_demodulation,[],[f1943,f1406])).

fof(f1943,plain,(
    ! [X12] : k6_subset_1(k1_relat_1(sK2),X12) = k1_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X12))) ),
    inference(resolution,[],[f1395,f1405])).

fof(f1405,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f900])).

fof(f900,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f816])).

fof(f816,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

fof(f1395,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f1263])).

fof(f2573,plain,(
    ~ r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))) ),
    inference(subsumption_resolution,[],[f2536,f2097])).

fof(f2097,plain,(
    ! [X259] : v1_relat_1(k4_xboole_0(sK2,X259)) ),
    inference(resolution,[],[f1395,f1603])).

fof(f1603,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1058])).

fof(f1058,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f692])).

fof(f692,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f2536,plain,
    ( ~ r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))))
    | ~ v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))) ),
    inference(trivial_inequality_removal,[],[f2532])).

fof(f2532,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))))
    | ~ v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))) ),
    inference(superposition,[],[f1935,f1441])).

fof(f1441,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f940])).

fof(f940,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f788])).

fof(f788,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f1935,plain,(
    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(forward_demodulation,[],[f1397,f1406])).

fof(f1397,plain,(
    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(cnf_transformation,[],[f1263])).
%------------------------------------------------------------------------------
