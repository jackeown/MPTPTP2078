%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:48 EST 2020

% Result     : Theorem 2.42s
% Output     : Refutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 265 expanded)
%              Number of leaves         :   19 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :  154 ( 483 expanded)
%              Number of equality atoms :   67 ( 119 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3159,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3156,f383])).

fof(f383,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),k9_relat_1(sK1,k10_relat_1(sK1,X0))) ),
    inference(backward_demodulation,[],[f265,f381])).

fof(f381,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k9_relat_1(k4_relat_1(sK1),X0) ),
    inference(backward_demodulation,[],[f271,f380])).

fof(f380,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k2_relat_1(k4_relat_1(k8_relat_1(X0,sK1))) ),
    inference(forward_demodulation,[],[f324,f221])).

fof(f221,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k1_relat_1(k8_relat_1(X0,sK1)) ),
    inference(forward_demodulation,[],[f220,f196])).

fof(f196,plain,(
    ! [X0] : k5_relat_1(sK1,k6_relat_1(X0)) = k8_relat_1(X0,sK1) ),
    inference(unit_resulting_resolution,[],[f89,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f89,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,
    ( ~ r1_tarski(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f59,f84])).

fof(f84,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f58])).

fof(f58,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f57])).

fof(f57,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t183_relat_1)).

fof(f220,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) = k10_relat_1(sK1,X0) ),
    inference(forward_demodulation,[],[f185,f99])).

fof(f99,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

fof(f53,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f185,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) = k10_relat_1(sK1,k1_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f93,f89,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f93,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f324,plain,(
    ! [X0] : k1_relat_1(k8_relat_1(X0,sK1)) = k2_relat_1(k4_relat_1(k8_relat_1(X0,sK1))) ),
    inference(unit_resulting_resolution,[],[f193,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f193,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK1)) ),
    inference(unit_resulting_resolution,[],[f89,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f271,plain,(
    ! [X0] : k9_relat_1(k4_relat_1(sK1),X0) = k2_relat_1(k4_relat_1(k8_relat_1(X0,sK1))) ),
    inference(backward_demodulation,[],[f247,f270])).

fof(f270,plain,(
    ! [X0] : k4_relat_1(k8_relat_1(X0,sK1)) = k7_relat_1(k4_relat_1(sK1),X0) ),
    inference(forward_demodulation,[],[f246,f218])).

fof(f218,plain,(
    ! [X0] : k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) = k4_relat_1(k8_relat_1(X0,sK1)) ),
    inference(forward_demodulation,[],[f217,f196])).

fof(f217,plain,(
    ! [X0] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f189,f98])).

fof(f98,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f189,plain,(
    ! [X0] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) = k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f93,f89,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f246,plain,(
    ! [X0] : k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) = k7_relat_1(k4_relat_1(sK1),X0) ),
    inference(unit_resulting_resolution,[],[f181,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f56])).

fof(f56,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f181,plain,(
    v1_relat_1(k4_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f89,f101])).

fof(f101,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f247,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) = k9_relat_1(k4_relat_1(sK1),X0) ),
    inference(unit_resulting_resolution,[],[f181,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f265,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),k9_relat_1(sK1,k9_relat_1(k4_relat_1(sK1),X0))) ),
    inference(forward_demodulation,[],[f264,f200])).

fof(f200,plain,(
    ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),X0)) ),
    inference(unit_resulting_resolution,[],[f89,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f125,f116])).

fof(f116,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f125,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(f264,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),X0)),k9_relat_1(sK1,k9_relat_1(k4_relat_1(sK1),X0))) ),
    inference(forward_demodulation,[],[f263,f183])).

fof(f183,plain,(
    k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f89,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f263,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(k1_relat_1(k4_relat_1(sK1)),k4_xboole_0(k1_relat_1(k4_relat_1(sK1)),X0)),k9_relat_1(sK1,k9_relat_1(k4_relat_1(sK1),X0))) ),
    inference(forward_demodulation,[],[f251,f182])).

fof(f182,plain,(
    sK1 = k4_relat_1(k4_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f89,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f251,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(k1_relat_1(k4_relat_1(sK1)),k4_xboole_0(k1_relat_1(k4_relat_1(sK1)),X0)),k9_relat_1(k4_relat_1(k4_relat_1(sK1)),k9_relat_1(k4_relat_1(sK1),X0))) ),
    inference(unit_resulting_resolution,[],[f181,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f127,f116])).

fof(f127,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_relat_1)).

fof(f3156,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f453,f3099])).

fof(f3099,plain,(
    ! [X1] : k2_relat_1(k8_relat_1(X1,sK1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_relat_1(sK1))) ),
    inference(superposition,[],[f200,f156])).

fof(f156,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f111,f116,f116])).

fof(f111,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f453,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k2_relat_1(sK1))),k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(backward_demodulation,[],[f180,f446])).

fof(f446,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k10_relat_1(k4_relat_1(sK1),X0) ),
    inference(backward_demodulation,[],[f302,f445])).

fof(f445,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k1_relat_1(k4_relat_1(k7_relat_1(sK1,X0))) ),
    inference(forward_demodulation,[],[f389,f198])).

fof(f198,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(unit_resulting_resolution,[],[f89,f124])).

fof(f389,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k4_relat_1(k7_relat_1(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f194,f103])).

fof(f194,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f89,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f302,plain,(
    ! [X0] : k10_relat_1(k4_relat_1(sK1),X0) = k1_relat_1(k4_relat_1(k7_relat_1(sK1,X0))) ),
    inference(forward_demodulation,[],[f301,f216])).

fof(f216,plain,(
    ! [X0] : k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(sK1,X0)) ),
    inference(forward_demodulation,[],[f215,f197])).

fof(f197,plain,(
    ! [X0] : k5_relat_1(k6_relat_1(X0),sK1) = k7_relat_1(sK1,X0) ),
    inference(unit_resulting_resolution,[],[f89,f123])).

fof(f215,plain,(
    ! [X0] : k4_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f191,f98])).

fof(f191,plain,(
    ! [X0] : k4_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k5_relat_1(k4_relat_1(sK1),k4_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f93,f89,f106])).

fof(f301,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK1),X0) ),
    inference(forward_demodulation,[],[f230,f99])).

fof(f230,plain,(
    ! [X0] : k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f93,f181,f105])).

fof(f180,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k2_relat_1(sK1))),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f153,f156])).

fof(f153,plain,(
    ~ r1_tarski(k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),sK0)),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))) ),
    inference(definition_unfolding,[],[f90,f116])).

fof(f90,plain,(
    ~ r1_tarski(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:49:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (19377)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.50  % (19366)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.50  % (19369)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (19365)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (19382)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.51  % (19390)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.51  % (19385)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (19374)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.51  % (19381)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.51  % (19373)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.13/0.51  % (19364)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.13/0.51  % (19386)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.13/0.52  % (19373)Refutation not found, incomplete strategy% (19373)------------------------------
% 1.13/0.52  % (19373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.52  % (19380)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.13/0.52  % (19370)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.13/0.52  % (19375)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.13/0.52  % (19372)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.13/0.52  % (19387)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.13/0.52  % (19371)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.13/0.52  % (19363)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.13/0.52  % (19376)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.13/0.52  % (19379)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.13/0.52  % (19367)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.13/0.53  % (19378)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.13/0.53  % (19392)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.13/0.53  % (19383)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.13/0.53  % (19389)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.24/0.53  % (19368)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.24/0.54  % (19391)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.24/0.54  % (19388)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.24/0.54  % (19373)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (19373)Memory used [KB]: 10746
% 1.24/0.54  % (19373)Time elapsed: 0.116 s
% 1.24/0.54  % (19373)------------------------------
% 1.24/0.54  % (19373)------------------------------
% 1.24/0.54  % (19379)Refutation not found, incomplete strategy% (19379)------------------------------
% 1.24/0.54  % (19379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (19379)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (19379)Memory used [KB]: 10618
% 1.24/0.54  % (19379)Time elapsed: 0.131 s
% 1.24/0.54  % (19379)------------------------------
% 1.24/0.54  % (19379)------------------------------
% 1.24/0.54  % (19391)Refutation not found, incomplete strategy% (19391)------------------------------
% 1.24/0.54  % (19391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (19391)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (19391)Memory used [KB]: 10746
% 1.24/0.54  % (19391)Time elapsed: 0.132 s
% 1.24/0.54  % (19391)------------------------------
% 1.24/0.54  % (19391)------------------------------
% 1.24/0.54  % (19384)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.91/0.66  % (19409)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.91/0.68  % (19410)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.42/0.70  % (19419)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.42/0.72  % (19374)Refutation found. Thanks to Tanya!
% 2.42/0.72  % SZS status Theorem for theBenchmark
% 2.42/0.72  % SZS output start Proof for theBenchmark
% 2.42/0.72  fof(f3159,plain,(
% 2.42/0.72    $false),
% 2.42/0.72    inference(subsumption_resolution,[],[f3156,f383])).
% 2.42/0.72  fof(f383,plain,(
% 2.42/0.72    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),k9_relat_1(sK1,k10_relat_1(sK1,X0)))) )),
% 2.42/0.72    inference(backward_demodulation,[],[f265,f381])).
% 2.42/0.72  fof(f381,plain,(
% 2.42/0.72    ( ! [X0] : (k10_relat_1(sK1,X0) = k9_relat_1(k4_relat_1(sK1),X0)) )),
% 2.42/0.72    inference(backward_demodulation,[],[f271,f380])).
% 2.42/0.72  fof(f380,plain,(
% 2.42/0.72    ( ! [X0] : (k10_relat_1(sK1,X0) = k2_relat_1(k4_relat_1(k8_relat_1(X0,sK1)))) )),
% 2.42/0.72    inference(forward_demodulation,[],[f324,f221])).
% 2.42/0.72  fof(f221,plain,(
% 2.42/0.72    ( ! [X0] : (k10_relat_1(sK1,X0) = k1_relat_1(k8_relat_1(X0,sK1))) )),
% 2.42/0.72    inference(forward_demodulation,[],[f220,f196])).
% 2.42/0.72  fof(f196,plain,(
% 2.42/0.72    ( ! [X0] : (k5_relat_1(sK1,k6_relat_1(X0)) = k8_relat_1(X0,sK1)) )),
% 2.42/0.72    inference(unit_resulting_resolution,[],[f89,f122])).
% 2.42/0.72  fof(f122,plain,(
% 2.42/0.72    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 2.42/0.72    inference(cnf_transformation,[],[f69])).
% 2.42/0.72  fof(f69,plain,(
% 2.42/0.72    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 2.42/0.72    inference(ennf_transformation,[],[f46])).
% 2.42/0.72  fof(f46,axiom,(
% 2.42/0.72    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 2.42/0.72  fof(f89,plain,(
% 2.42/0.72    v1_relat_1(sK1)),
% 2.42/0.72    inference(cnf_transformation,[],[f85])).
% 2.42/0.72  fof(f85,plain,(
% 2.42/0.72    ~r1_tarski(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 2.42/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f59,f84])).
% 2.42/0.72  fof(f84,plain,(
% 2.42/0.72    ? [X0,X1] : (~r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0))) & v1_relat_1(X1)) => (~r1_tarski(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 2.42/0.72    introduced(choice_axiom,[])).
% 2.42/0.72  fof(f59,plain,(
% 2.42/0.72    ? [X0,X1] : (~r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 2.42/0.72    inference(ennf_transformation,[],[f58])).
% 2.42/0.72  fof(f58,negated_conjecture,(
% 2.42/0.72    ~! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0))))),
% 2.42/0.72    inference(negated_conjecture,[],[f57])).
% 2.42/0.72  fof(f57,conjecture,(
% 2.42/0.72    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k3_xboole_0(k2_relat_1(X1),X0),k10_relat_1(k4_relat_1(X1),k10_relat_1(X1,X0))))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t183_relat_1)).
% 2.42/0.72  fof(f220,plain,(
% 2.42/0.72    ( ! [X0] : (k1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) = k10_relat_1(sK1,X0)) )),
% 2.42/0.72    inference(forward_demodulation,[],[f185,f99])).
% 2.42/0.72  fof(f99,plain,(
% 2.42/0.72    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.42/0.72    inference(cnf_transformation,[],[f53])).
% 2.42/0.72  fof(f53,axiom,(
% 2.42/0.72    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.42/0.72  fof(f185,plain,(
% 2.42/0.72    ( ! [X0] : (k1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) = k10_relat_1(sK1,k1_relat_1(k6_relat_1(X0)))) )),
% 2.42/0.72    inference(unit_resulting_resolution,[],[f93,f89,f105])).
% 2.42/0.72  fof(f105,plain,(
% 2.42/0.72    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 2.42/0.72    inference(cnf_transformation,[],[f63])).
% 2.42/0.72  fof(f63,plain,(
% 2.42/0.72    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.42/0.72    inference(ennf_transformation,[],[f49])).
% 2.42/0.72  fof(f49,axiom,(
% 2.42/0.72    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 2.42/0.72  fof(f93,plain,(
% 2.42/0.72    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.42/0.72    inference(cnf_transformation,[],[f38])).
% 2.42/0.72  fof(f38,axiom,(
% 2.42/0.72    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 2.42/0.72  fof(f324,plain,(
% 2.42/0.72    ( ! [X0] : (k1_relat_1(k8_relat_1(X0,sK1)) = k2_relat_1(k4_relat_1(k8_relat_1(X0,sK1)))) )),
% 2.42/0.72    inference(unit_resulting_resolution,[],[f193,f104])).
% 2.42/0.72  fof(f104,plain,(
% 2.42/0.72    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 2.42/0.72    inference(cnf_transformation,[],[f62])).
% 2.42/0.72  fof(f62,plain,(
% 2.42/0.72    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.42/0.72    inference(ennf_transformation,[],[f50])).
% 2.42/0.72  fof(f50,axiom,(
% 2.42/0.72    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 2.42/0.72  fof(f193,plain,(
% 2.42/0.72    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK1))) )),
% 2.42/0.72    inference(unit_resulting_resolution,[],[f89,f118])).
% 2.42/0.72  fof(f118,plain,(
% 2.42/0.72    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 2.42/0.72    inference(cnf_transformation,[],[f65])).
% 2.42/0.72  fof(f65,plain,(
% 2.42/0.72    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 2.42/0.72    inference(ennf_transformation,[],[f40])).
% 2.42/0.72  fof(f40,axiom,(
% 2.42/0.72    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 2.42/0.72  fof(f271,plain,(
% 2.42/0.72    ( ! [X0] : (k9_relat_1(k4_relat_1(sK1),X0) = k2_relat_1(k4_relat_1(k8_relat_1(X0,sK1)))) )),
% 2.42/0.72    inference(backward_demodulation,[],[f247,f270])).
% 2.42/0.72  fof(f270,plain,(
% 2.42/0.72    ( ! [X0] : (k4_relat_1(k8_relat_1(X0,sK1)) = k7_relat_1(k4_relat_1(sK1),X0)) )),
% 2.42/0.72    inference(forward_demodulation,[],[f246,f218])).
% 2.42/0.72  fof(f218,plain,(
% 2.42/0.72    ( ! [X0] : (k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) = k4_relat_1(k8_relat_1(X0,sK1))) )),
% 2.42/0.72    inference(forward_demodulation,[],[f217,f196])).
% 2.42/0.72  fof(f217,plain,(
% 2.42/0.72    ( ! [X0] : (k4_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1))) )),
% 2.42/0.72    inference(forward_demodulation,[],[f189,f98])).
% 2.42/0.72  fof(f98,plain,(
% 2.42/0.72    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 2.42/0.72    inference(cnf_transformation,[],[f54])).
% 2.42/0.72  fof(f54,axiom,(
% 2.42/0.72    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 2.42/0.72  fof(f189,plain,(
% 2.42/0.72    ( ! [X0] : (k4_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) = k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(sK1))) )),
% 2.42/0.72    inference(unit_resulting_resolution,[],[f93,f89,f106])).
% 2.42/0.72  fof(f106,plain,(
% 2.42/0.72    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.42/0.72    inference(cnf_transformation,[],[f64])).
% 2.42/0.72  fof(f64,plain,(
% 2.42/0.72    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.42/0.72    inference(ennf_transformation,[],[f51])).
% 2.42/0.72  fof(f51,axiom,(
% 2.42/0.72    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 2.42/0.72  fof(f246,plain,(
% 2.42/0.72    ( ! [X0] : (k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) = k7_relat_1(k4_relat_1(sK1),X0)) )),
% 2.42/0.72    inference(unit_resulting_resolution,[],[f181,f123])).
% 2.42/0.72  fof(f123,plain,(
% 2.42/0.72    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.42/0.72    inference(cnf_transformation,[],[f70])).
% 2.42/0.72  fof(f70,plain,(
% 2.42/0.72    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.42/0.72    inference(ennf_transformation,[],[f56])).
% 2.42/0.72  fof(f56,axiom,(
% 2.42/0.72    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.42/0.72  fof(f181,plain,(
% 2.42/0.72    v1_relat_1(k4_relat_1(sK1))),
% 2.42/0.72    inference(unit_resulting_resolution,[],[f89,f101])).
% 2.42/0.72  fof(f101,plain,(
% 2.42/0.72    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.42/0.72    inference(cnf_transformation,[],[f60])).
% 2.42/0.72  fof(f60,plain,(
% 2.42/0.72    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.42/0.72    inference(ennf_transformation,[],[f37])).
% 2.42/0.72  fof(f37,axiom,(
% 2.42/0.72    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 2.42/0.72  fof(f247,plain,(
% 2.42/0.72    ( ! [X0] : (k2_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) = k9_relat_1(k4_relat_1(sK1),X0)) )),
% 2.42/0.72    inference(unit_resulting_resolution,[],[f181,f124])).
% 2.42/0.72  fof(f124,plain,(
% 2.42/0.72    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.42/0.72    inference(cnf_transformation,[],[f71])).
% 2.42/0.72  fof(f71,plain,(
% 2.42/0.72    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.42/0.72    inference(ennf_transformation,[],[f47])).
% 2.42/0.72  fof(f47,axiom,(
% 2.42/0.72    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.42/0.72  fof(f265,plain,(
% 2.42/0.72    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),k9_relat_1(sK1,k9_relat_1(k4_relat_1(sK1),X0)))) )),
% 2.42/0.72    inference(forward_demodulation,[],[f264,f200])).
% 2.42/0.72  fof(f200,plain,(
% 2.42/0.72    ( ! [X0] : (k2_relat_1(k8_relat_1(X0,sK1)) = k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),X0))) )),
% 2.42/0.72    inference(unit_resulting_resolution,[],[f89,f162])).
% 2.42/0.72  fof(f162,plain,(
% 2.42/0.72    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) )),
% 2.42/0.72    inference(definition_unfolding,[],[f125,f116])).
% 2.42/0.72  fof(f116,plain,(
% 2.42/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.42/0.72    inference(cnf_transformation,[],[f28])).
% 2.42/0.72  fof(f28,axiom,(
% 2.42/0.72    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.42/0.72  fof(f125,plain,(
% 2.42/0.72    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.42/0.72    inference(cnf_transformation,[],[f72])).
% 2.42/0.72  fof(f72,plain,(
% 2.42/0.72    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.42/0.72    inference(ennf_transformation,[],[f45])).
% 2.42/0.72  fof(f45,axiom,(
% 2.42/0.72    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).
% 2.42/0.72  fof(f264,plain,(
% 2.42/0.72    ( ! [X0] : (r1_tarski(k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),X0)),k9_relat_1(sK1,k9_relat_1(k4_relat_1(sK1),X0)))) )),
% 2.42/0.72    inference(forward_demodulation,[],[f263,f183])).
% 2.42/0.72  fof(f183,plain,(
% 2.42/0.72    k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1))),
% 2.42/0.72    inference(unit_resulting_resolution,[],[f89,f103])).
% 2.42/0.72  fof(f103,plain,(
% 2.42/0.72    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 2.42/0.72    inference(cnf_transformation,[],[f62])).
% 2.42/0.72  fof(f263,plain,(
% 2.42/0.72    ( ! [X0] : (r1_tarski(k4_xboole_0(k1_relat_1(k4_relat_1(sK1)),k4_xboole_0(k1_relat_1(k4_relat_1(sK1)),X0)),k9_relat_1(sK1,k9_relat_1(k4_relat_1(sK1),X0)))) )),
% 2.42/0.72    inference(forward_demodulation,[],[f251,f182])).
% 2.42/0.72  fof(f182,plain,(
% 2.42/0.72    sK1 = k4_relat_1(k4_relat_1(sK1))),
% 2.42/0.72    inference(unit_resulting_resolution,[],[f89,f102])).
% 2.42/0.72  fof(f102,plain,(
% 2.42/0.72    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 2.42/0.72    inference(cnf_transformation,[],[f61])).
% 2.42/0.72  fof(f61,plain,(
% 2.42/0.72    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.42/0.72    inference(ennf_transformation,[],[f42])).
% 2.42/0.72  fof(f42,axiom,(
% 2.42/0.72    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 2.42/0.72  fof(f251,plain,(
% 2.42/0.72    ( ! [X0] : (r1_tarski(k4_xboole_0(k1_relat_1(k4_relat_1(sK1)),k4_xboole_0(k1_relat_1(k4_relat_1(sK1)),X0)),k9_relat_1(k4_relat_1(k4_relat_1(sK1)),k9_relat_1(k4_relat_1(sK1),X0)))) )),
% 2.42/0.72    inference(unit_resulting_resolution,[],[f181,f164])).
% 2.42/0.72  fof(f164,plain,(
% 2.42/0.72    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) | ~v1_relat_1(X1)) )),
% 2.42/0.72    inference(definition_unfolding,[],[f127,f116])).
% 2.42/0.72  fof(f127,plain,(
% 2.42/0.72    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) | ~v1_relat_1(X1)) )),
% 2.42/0.72    inference(cnf_transformation,[],[f74])).
% 2.42/0.72  fof(f74,plain,(
% 2.42/0.72    ! [X0,X1] : (r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.42/0.72    inference(ennf_transformation,[],[f48])).
% 2.42/0.72  fof(f48,axiom,(
% 2.42/0.72    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_relat_1)).
% 2.42/0.72  fof(f3156,plain,(
% 2.42/0.72    ~r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 2.42/0.72    inference(backward_demodulation,[],[f453,f3099])).
% 2.42/0.72  fof(f3099,plain,(
% 2.42/0.72    ( ! [X1] : (k2_relat_1(k8_relat_1(X1,sK1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_relat_1(sK1)))) )),
% 2.42/0.72    inference(superposition,[],[f200,f156])).
% 2.42/0.72  fof(f156,plain,(
% 2.42/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.42/0.72    inference(definition_unfolding,[],[f111,f116,f116])).
% 2.42/0.72  fof(f111,plain,(
% 2.42/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.42/0.72    inference(cnf_transformation,[],[f2])).
% 2.42/0.72  fof(f2,axiom,(
% 2.42/0.72    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.42/0.72  fof(f453,plain,(
% 2.42/0.72    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k2_relat_1(sK1))),k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 2.42/0.72    inference(backward_demodulation,[],[f180,f446])).
% 2.42/0.72  fof(f446,plain,(
% 2.42/0.72    ( ! [X0] : (k9_relat_1(sK1,X0) = k10_relat_1(k4_relat_1(sK1),X0)) )),
% 2.42/0.72    inference(backward_demodulation,[],[f302,f445])).
% 2.42/0.72  fof(f445,plain,(
% 2.42/0.72    ( ! [X0] : (k9_relat_1(sK1,X0) = k1_relat_1(k4_relat_1(k7_relat_1(sK1,X0)))) )),
% 2.42/0.72    inference(forward_demodulation,[],[f389,f198])).
% 2.42/0.72  fof(f198,plain,(
% 2.42/0.72    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 2.42/0.72    inference(unit_resulting_resolution,[],[f89,f124])).
% 2.42/0.72  fof(f389,plain,(
% 2.42/0.72    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k4_relat_1(k7_relat_1(sK1,X0)))) )),
% 2.42/0.72    inference(unit_resulting_resolution,[],[f194,f103])).
% 2.42/0.72  fof(f194,plain,(
% 2.42/0.72    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 2.42/0.72    inference(unit_resulting_resolution,[],[f89,f119])).
% 2.42/0.72  fof(f119,plain,(
% 2.42/0.72    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.42/0.72    inference(cnf_transformation,[],[f66])).
% 2.42/0.72  fof(f66,plain,(
% 2.42/0.72    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.42/0.72    inference(ennf_transformation,[],[f39])).
% 2.42/0.72  fof(f39,axiom,(
% 2.42/0.72    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.42/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.42/0.72  fof(f302,plain,(
% 2.42/0.72    ( ! [X0] : (k10_relat_1(k4_relat_1(sK1),X0) = k1_relat_1(k4_relat_1(k7_relat_1(sK1,X0)))) )),
% 2.42/0.72    inference(forward_demodulation,[],[f301,f216])).
% 2.42/0.72  fof(f216,plain,(
% 2.42/0.72    ( ! [X0] : (k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(sK1,X0))) )),
% 2.42/0.72    inference(forward_demodulation,[],[f215,f197])).
% 2.42/0.72  fof(f197,plain,(
% 2.42/0.72    ( ! [X0] : (k5_relat_1(k6_relat_1(X0),sK1) = k7_relat_1(sK1,X0)) )),
% 2.42/0.72    inference(unit_resulting_resolution,[],[f89,f123])).
% 2.42/0.72  fof(f215,plain,(
% 2.42/0.72    ( ! [X0] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0))) )),
% 2.42/0.72    inference(forward_demodulation,[],[f191,f98])).
% 2.42/0.72  fof(f191,plain,(
% 2.42/0.72    ( ! [X0] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),sK1)) = k5_relat_1(k4_relat_1(sK1),k4_relat_1(k6_relat_1(X0)))) )),
% 2.42/0.72    inference(unit_resulting_resolution,[],[f93,f89,f106])).
% 2.42/0.72  fof(f301,plain,(
% 2.42/0.72    ( ! [X0] : (k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK1),X0)) )),
% 2.42/0.72    inference(forward_demodulation,[],[f230,f99])).
% 2.42/0.72  fof(f230,plain,(
% 2.42/0.72    ( ! [X0] : (k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(k6_relat_1(X0)))) )),
% 2.42/0.72    inference(unit_resulting_resolution,[],[f93,f181,f105])).
% 2.42/0.72  fof(f180,plain,(
% 2.42/0.72    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k2_relat_1(sK1))),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0)))),
% 2.42/0.72    inference(forward_demodulation,[],[f153,f156])).
% 2.42/0.72  fof(f153,plain,(
% 2.42/0.72    ~r1_tarski(k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),sK0)),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0)))),
% 2.42/0.72    inference(definition_unfolding,[],[f90,f116])).
% 2.42/0.72  fof(f90,plain,(
% 2.42/0.72    ~r1_tarski(k3_xboole_0(k2_relat_1(sK1),sK0),k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,sK0)))),
% 2.42/0.72    inference(cnf_transformation,[],[f85])).
% 2.42/0.72  % SZS output end Proof for theBenchmark
% 2.42/0.72  % (19374)------------------------------
% 2.42/0.72  % (19374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.42/0.72  % (19374)Termination reason: Refutation
% 2.42/0.72  
% 2.42/0.72  % (19374)Memory used [KB]: 9338
% 2.42/0.72  % (19374)Time elapsed: 0.307 s
% 2.42/0.72  % (19374)------------------------------
% 2.42/0.72  % (19374)------------------------------
% 2.42/0.74  % (19362)Success in time 0.373 s
%------------------------------------------------------------------------------
