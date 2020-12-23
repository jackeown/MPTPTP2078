%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0579+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:38 EST 2020

% Result     : Theorem 39.23s
% Output     : Refutation 39.78s
% Verified   : 
% Statistics : Number of formulae       :  201 (1821 expanded)
%              Number of leaves         :   37 ( 582 expanded)
%              Depth                    :   27
%              Number of atoms          :  291 (2448 expanded)
%              Number of equality atoms :  153 (1434 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41887,plain,(
    $false ),
    inference(subsumption_resolution,[],[f41797,f40321])).

fof(f40321,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),k9_relat_1(sK1,k10_relat_1(sK1,X0))) ),
    inference(backward_demodulation,[],[f37839,f40310])).

fof(f40310,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k9_relat_1(k4_relat_1(sK1),X0) ),
    inference(backward_demodulation,[],[f26216,f40309])).

fof(f40309,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k2_relat_1(k4_relat_1(k8_relat_1(X0,sK1))) ),
    inference(forward_demodulation,[],[f39243,f18839])).

fof(f18839,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k1_relat_1(k8_relat_1(X0,sK1)) ),
    inference(forward_demodulation,[],[f18838,f6879])).

fof(f6879,plain,(
    ! [X0] : k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f1935,f2268])).

fof(f2268,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f993])).

fof(f993,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f710])).

fof(f710,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f1935,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1499])).

fof(f1499,plain,
    ( ~ r1_tarski(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f854,f1498])).

fof(f1498,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f854,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f770])).

fof(f770,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f769])).

fof(f769,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t183_relat_1)).

fof(f18838,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f18717,f1998])).

fof(f1998,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f812])).

fof(f812,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f18717,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) = k10_relat_1(sK1,k1_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f1935,f1952,f2047])).

fof(f2047,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f897])).

fof(f897,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f768])).

fof(f768,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f1952,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f659])).

fof(f659,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f39243,plain,(
    ! [X0] : k1_relat_1(k8_relat_1(X0,sK1)) = k2_relat_1(k4_relat_1(k8_relat_1(X0,sK1))) ),
    inference(unit_resulting_resolution,[],[f4665,f2039])).

fof(f2039,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f889])).

fof(f889,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f787])).

fof(f787,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f4665,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK1)) ),
    inference(unit_resulting_resolution,[],[f1935,f2252])).

fof(f2252,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f977])).

fof(f977,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f661])).

fof(f661,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f26216,plain,(
    ! [X0] : k9_relat_1(k4_relat_1(sK1),X0) = k2_relat_1(k4_relat_1(k8_relat_1(X0,sK1))) ),
    inference(backward_demodulation,[],[f6860,f26211])).

fof(f26211,plain,(
    ! [X0] : k7_relat_1(k4_relat_1(sK1),X0) = k4_relat_1(k8_relat_1(X0,sK1)) ),
    inference(backward_demodulation,[],[f6901,f26210])).

fof(f26210,plain,(
    ! [X0] : k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) = k4_relat_1(k8_relat_1(X0,sK1)) ),
    inference(forward_demodulation,[],[f26209,f6879])).

fof(f26209,plain,(
    ! [X0] : k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) = k4_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f25907,f1984])).

fof(f1984,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f813])).

fof(f813,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f25907,plain,(
    ! [X0] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) = k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1935,f1952,f2051])).

fof(f2051,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f901])).

fof(f901,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f802])).

fof(f802,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f6901,plain,(
    ! [X0] : k7_relat_1(k4_relat_1(sK1),X0) = k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f4548,f2269])).

fof(f2269,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f994])).

fof(f994,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f832])).

fof(f832,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f4548,plain,(
    v1_relat_1(k4_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1935,f2017])).

fof(f2017,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f869])).

fof(f869,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f657])).

fof(f657,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f6860,plain,(
    ! [X0] : k9_relat_1(k4_relat_1(sK1),X0) = k2_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) ),
    inference(unit_resulting_resolution,[],[f4548,f2267])).

fof(f2267,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f992])).

fof(f992,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f734])).

fof(f734,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f37839,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),k9_relat_1(sK1,k9_relat_1(k4_relat_1(sK1),X0))) ),
    inference(forward_demodulation,[],[f37838,f19030])).

fof(f19030,plain,(
    ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k9_relat_1(k6_relat_1(X0),k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f18909,f6879])).

fof(f18909,plain,(
    ! [X0] : k2_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) = k9_relat_1(k6_relat_1(X0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1935,f1952,f2048])).

fof(f2048,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f898])).

fof(f898,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f748])).

fof(f748,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f37838,plain,(
    ! [X0] : r1_tarski(k9_relat_1(k6_relat_1(X0),k2_relat_1(sK1)),k9_relat_1(sK1,k9_relat_1(k4_relat_1(sK1),X0))) ),
    inference(forward_demodulation,[],[f37837,f4994])).

fof(f4994,plain,(
    k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1935,f2038])).

fof(f2038,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f889])).

fof(f37837,plain,(
    ! [X0] : r1_tarski(k9_relat_1(k6_relat_1(X0),k1_relat_1(k4_relat_1(sK1))),k9_relat_1(sK1,k9_relat_1(k4_relat_1(sK1),X0))) ),
    inference(forward_demodulation,[],[f37818,f4778])).

fof(f4778,plain,(
    sK1 = k4_relat_1(k4_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1935,f2023])).

fof(f2023,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f875])).

fof(f875,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f687])).

fof(f687,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f37818,plain,(
    ! [X0] : r1_tarski(k9_relat_1(k6_relat_1(X0),k1_relat_1(k4_relat_1(sK1))),k9_relat_1(k4_relat_1(k4_relat_1(sK1)),k9_relat_1(k4_relat_1(sK1),X0))) ),
    inference(unit_resulting_resolution,[],[f4548,f33726])).

fof(f33726,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(k6_relat_1(X0),k1_relat_1(X1)),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(backward_demodulation,[],[f31329,f33568])).

fof(f33568,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f33567,f6859])).

fof(f6859,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(unit_resulting_resolution,[],[f1952,f2267])).

fof(f33567,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f33566,f6916])).

fof(f6916,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f6876,f6900])).

fof(f6900,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f1952,f2269])).

fof(f6876,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f1952,f2268])).

fof(f33566,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f33459,f1999])).

fof(f1999,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f812])).

fof(f33459,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X1))) ),
    inference(unit_resulting_resolution,[],[f1952,f31333])).

fof(f31333,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(backward_demodulation,[],[f28427,f31089])).

fof(f31089,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X1),X0) = k8_subset_1(X0,X0,X1) ),
    inference(forward_demodulation,[],[f31088,f18848])).

fof(f18848,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f18847,f6900])).

fof(f18847,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f18714,f1998])).

fof(f18714,plain,(
    ! [X0,X1] : k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) ),
    inference(unit_resulting_resolution,[],[f1952,f1952,f2047])).

fof(f31088,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k8_subset_1(X0,X0,X1) ),
    inference(forward_demodulation,[],[f31077,f1998])).

fof(f31077,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k8_subset_1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1) ),
    inference(unit_resulting_resolution,[],[f1952,f28424])).

fof(f28424,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k8_subset_1(k1_relat_1(X1),k1_relat_1(X1),X0) ) ),
    inference(backward_demodulation,[],[f10382,f28161])).

fof(f28161,plain,(
    ! [X0,X1] : k3_subset_1(X0,k6_subset_1(X0,X1)) = k8_subset_1(X0,X0,X1) ),
    inference(unit_resulting_resolution,[],[f4220,f10329])).

fof(f10329,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k8_subset_1(X0,X1,X2) = k3_subset_1(X1,k6_subset_1(X1,X2)) ) ),
    inference(backward_demodulation,[],[f4439,f10267])).

fof(f10267,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k3_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f2170,f3443])).

fof(f3443,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f2375,f2177])).

fof(f2177,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f493])).

fof(f493,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f2375,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1111])).

fof(f1111,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f2170,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f469])).

fof(f469,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f4439,plain,(
    ! [X2,X0,X1] :
      ( k8_subset_1(X0,X1,X2) = k6_subset_1(X1,k6_subset_1(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f3611,f3352])).

fof(f3352,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f2201,f3227,f2177,f2177])).

fof(f3227,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f2191,f3225])).

fof(f3225,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f2190,f3224])).

fof(f3224,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f2638,f3223])).

fof(f3223,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f2965,f3222])).

fof(f3222,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f3048,f3221])).

fof(f3221,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f3073,f3097])).

fof(f3097,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f260])).

fof(f260,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f3073,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f259])).

fof(f259,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f3048,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f258])).

fof(f258,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f2965,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f257])).

fof(f257,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f2638,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f256])).

fof(f256,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f2190,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f255])).

fof(f255,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f2191,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f587])).

fof(f587,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f2201,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f3611,plain,(
    ! [X2,X0,X1] :
      ( k8_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f2756,f3227])).

fof(f2756,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1339])).

fof(f1339,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f495])).

fof(f495,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k8_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_subset_1)).

fof(f4220,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f3268,f3253])).

fof(f3253,plain,(
    ! [X0] : k3_subset_1(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f1959,f3233])).

fof(f3233,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f1989,f3232])).

fof(f3232,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f1958,f1939])).

fof(f1939,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f1958,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f458])).

fof(f458,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f1989,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f502])).

fof(f502,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f1959,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f460])).

fof(f460,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f3268,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,o_0_0_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f1977,f3233])).

fof(f1977,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f465])).

fof(f465,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f10382,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_subset_1(k1_relat_1(X1),k6_subset_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(backward_demodulation,[],[f4285,f10267])).

fof(f4285,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k6_subset_1(k1_relat_1(X1),k6_subset_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f3396,f3352])).

fof(f3396,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f2275,f3227])).

fof(f2275,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1000])).

fof(f1000,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f828])).

fof(f828,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f28427,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k8_subset_1(k2_relat_1(X1),k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(backward_demodulation,[],[f10385,f28161])).

fof(f10385,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_subset_1(k2_relat_1(X1),k6_subset_1(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(backward_demodulation,[],[f4284,f10267])).

fof(f4284,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k6_subset_1(k2_relat_1(X1),k6_subset_1(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f3395,f3352])).

fof(f3395,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k6_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f2274,f3227])).

fof(f2274,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f999])).

fof(f999,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f706])).

fof(f706,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(f31329,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),k1_relat_1(X1)),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(backward_demodulation,[],[f28426,f31089])).

fof(f28426,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_subset_1(k1_relat_1(X1),k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(backward_demodulation,[],[f10380,f28161])).

fof(f10380,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(k1_relat_1(X1),k6_subset_1(k1_relat_1(X1),X0)),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(backward_demodulation,[],[f4290,f10267])).

fof(f4290,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k1_relat_1(X1),k6_subset_1(k1_relat_1(X1),X0)),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f3401,f3352])).

fof(f3401,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f2280,f3227])).

fof(f2280,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1005])).

fof(f1005,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f751])).

fof(f751,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_relat_1)).

fof(f41797,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f33479,f41769])).

fof(f41769,plain,(
    ! [X0] : k10_relat_1(k4_relat_1(sK1),X0) = k9_relat_1(sK1,X0) ),
    inference(backward_demodulation,[],[f26075,f41768])).

fof(f41768,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k1_relat_1(k4_relat_1(k7_relat_1(sK1,X0))) ),
    inference(forward_demodulation,[],[f40500,f6862])).

fof(f6862,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k2_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f1935,f2267])).

fof(f40500,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k4_relat_1(k7_relat_1(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f4673,f2038])).

fof(f4673,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f1935,f2253])).

fof(f2253,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f978])).

fof(f978,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f660])).

fof(f660,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f26075,plain,(
    ! [X0] : k10_relat_1(k4_relat_1(sK1),X0) = k1_relat_1(k4_relat_1(k7_relat_1(sK1,X0))) ),
    inference(backward_demodulation,[],[f18845,f26066])).

fof(f26066,plain,(
    ! [X0] : k8_relat_1(X0,k4_relat_1(sK1)) = k4_relat_1(k7_relat_1(sK1,X0)) ),
    inference(backward_demodulation,[],[f6877,f26065])).

fof(f26065,plain,(
    ! [X0] : k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(sK1,X0)) ),
    inference(forward_demodulation,[],[f26064,f6903])).

fof(f6903,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) ),
    inference(unit_resulting_resolution,[],[f1935,f2269])).

fof(f26064,plain,(
    ! [X0] : k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) ),
    inference(forward_demodulation,[],[f25931,f1984])).

fof(f25931,plain,(
    ! [X0] : k4_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k5_relat_1(k4_relat_1(sK1),k4_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f1952,f1935,f2051])).

fof(f6877,plain,(
    ! [X0] : k8_relat_1(X0,k4_relat_1(sK1)) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f4548,f2268])).

fof(f18845,plain,(
    ! [X0] : k10_relat_1(k4_relat_1(sK1),X0) = k1_relat_1(k8_relat_1(X0,k4_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f18844,f6877])).

fof(f18844,plain,(
    ! [X0] : k10_relat_1(k4_relat_1(sK1),X0) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f18715,f1998])).

fof(f18715,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f4548,f1952,f2047])).

fof(f33479,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f31460,f33473])).

fof(f33473,plain,(
    ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k1_relat_1(k4_relat_1(k8_relat_1(X0,sK1))) ),
    inference(backward_demodulation,[],[f26222,f33462])).

fof(f33462,plain,(
    ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1935,f31333])).

fof(f26222,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),k2_relat_1(sK1)) = k1_relat_1(k4_relat_1(k8_relat_1(X0,sK1))) ),
    inference(backward_demodulation,[],[f18824,f26211])).

fof(f18824,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f18823,f6901])).

fof(f18823,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1))) = k10_relat_1(k6_relat_1(X0),k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f18723,f4994])).

fof(f18723,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k4_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f1952,f4548,f2047])).

fof(f31460,plain,(
    ~ r1_tarski(k1_relat_1(k4_relat_1(k8_relat_1(sK0,sK1))),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f31391,f26222])).

fof(f31391,plain,(
    ~ r1_tarski(k10_relat_1(k6_relat_1(sK0),k2_relat_1(sK1)),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f28599,f31091])).

fof(f31091,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X1),X0) = k8_subset_1(X0,X1,X0) ),
    inference(backward_demodulation,[],[f19840,f31089])).

fof(f19840,plain,(
    ! [X0,X1] : k8_subset_1(X0,X0,X1) = k8_subset_1(X0,X1,X0) ),
    inference(unit_resulting_resolution,[],[f4220,f2758])).

fof(f2758,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k8_subset_1(X0,X1,X2) = k8_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f1341])).

fof(f1341,plain,(
    ! [X0,X1,X2] :
      ( k8_subset_1(X0,X1,X2) = k8_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f453])).

fof(f453,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_subset_1(X0,X1,X2) = k8_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k8_subset_1)).

fof(f28599,plain,(
    ~ r1_tarski(k8_subset_1(k2_relat_1(sK1),sK0,k2_relat_1(sK1)),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f28429,f19840])).

fof(f28429,plain,(
    ~ r1_tarski(k8_subset_1(k2_relat_1(sK1),k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f10383,f28161])).

fof(f10383,plain,(
    ~ r1_tarski(k3_subset_1(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),sK0)),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f4243,f10267])).

fof(f4243,plain,(
    ~ r1_tarski(k6_subset_1(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),sK0)),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f3235,f3352])).

fof(f3235,plain,(
    ~ r1_tarski(k1_setfam_1(k6_enumset1(k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),k2_relat_1(sK1),sK0)),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))) ),
    inference(definition_unfolding,[],[f1936,f3227])).

fof(f1936,plain,(
    ~ r1_tarski(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f1499])).
%------------------------------------------------------------------------------
