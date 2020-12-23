%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:00 EST 2020

% Result     : Theorem 4.47s
% Output     : Refutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 226 expanded)
%              Number of leaves         :   15 (  67 expanded)
%              Depth                    :   19
%              Number of atoms          :  200 ( 483 expanded)
%              Number of equality atoms :   65 ( 164 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2847,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2843,f48])).

fof(f48,plain,(
    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
            & r1_tarski(X1,X2) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X2,X1] :
        ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
        & r1_tarski(X1,X2) )
   => ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f2843,plain,(
    k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1) ),
    inference(superposition,[],[f320,f2785])).

fof(f2785,plain,(
    sK1 = k9_relat_1(k6_relat_1(sK2),sK1) ),
    inference(resolution,[],[f2782,f309])).

fof(f309,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK1,k9_relat_1(k6_relat_1(X3),sK1))
      | sK1 = k9_relat_1(k6_relat_1(X3),sK1) ) ),
    inference(resolution,[],[f303,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f303,plain,(
    ! [X0] : r1_tarski(k9_relat_1(k6_relat_1(X0),sK1),sK1) ),
    inference(backward_demodulation,[],[f281,f302])).

fof(f302,plain,(
    ! [X7] : k9_relat_1(k6_relat_1(X7),sK1) = k9_relat_1(k7_relat_1(k6_relat_1(X7),sK1),sK2) ),
    inference(forward_demodulation,[],[f301,f104])).

fof(f104,plain,(
    ! [X2,X3] : k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2) ),
    inference(subsumption_resolution,[],[f103,f49])).

fof(f49,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f103,plain,(
    ! [X2,X3] :
      ( k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2)
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(subsumption_resolution,[],[f101,f49])).

fof(f101,plain,(
    ! [X2,X3] :
      ( k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2)
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f63,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f301,plain,(
    ! [X7] : k9_relat_1(k8_relat_1(X7,k6_relat_1(sK1)),sK2) = k9_relat_1(k6_relat_1(X7),sK1) ),
    inference(subsumption_resolution,[],[f287,f49])).

fof(f287,plain,(
    ! [X7] :
      ( k9_relat_1(k8_relat_1(X7,k6_relat_1(sK1)),sK2) = k9_relat_1(k6_relat_1(X7),sK1)
      | ~ v1_relat_1(k6_relat_1(sK1)) ) ),
    inference(superposition,[],[f157,f171])).

fof(f171,plain,(
    sK1 = k9_relat_1(k6_relat_1(sK1),sK2) ),
    inference(forward_demodulation,[],[f170,f51])).

fof(f51,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f170,plain,(
    k9_relat_1(k6_relat_1(sK1),sK2) = k2_relat_1(k6_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f167,f49])).

fof(f167,plain,
    ( k9_relat_1(k6_relat_1(sK1),sK2) = k2_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(superposition,[],[f64,f165])).

fof(f165,plain,(
    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK2) ),
    inference(resolution,[],[f130,f47])).

fof(f47,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(subsumption_resolution,[],[f128,f49])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f65,f50])).

fof(f50,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) = k9_relat_1(k8_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f156,f49])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) = k9_relat_1(k8_relat_1(X1,X0),X2)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) = k9_relat_1(k8_relat_1(X1,X0),X2)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f66,f62])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

fof(f281,plain,(
    ! [X0] : r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X0),sK1),sK2),sK1) ),
    inference(subsumption_resolution,[],[f278,f49])).

fof(f278,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X0),sK1),sK2),sK1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f240,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f240,plain,(
    ! [X2] :
      ( ~ v1_relat_1(k7_relat_1(k6_relat_1(X2),sK1))
      | r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X2),sK1),sK2),sK1) ) ),
    inference(resolution,[],[f195,f106])).

fof(f106,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) ),
    inference(subsumption_resolution,[],[f105,f49])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f60,f104])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

fof(f195,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k6_relat_1(sK1))
      | r1_tarski(k9_relat_1(X0,sK2),sK1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f193,f49])).

fof(f193,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(X0,sK2),sK1)
      | ~ r1_tarski(X0,k6_relat_1(sK1))
      | ~ v1_relat_1(k6_relat_1(sK1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f67,f171])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

fof(f2782,plain,(
    r1_tarski(sK1,k9_relat_1(k6_relat_1(sK2),sK1)) ),
    inference(subsumption_resolution,[],[f2770,f49])).

fof(f2770,plain,
    ( r1_tarski(sK1,k9_relat_1(k6_relat_1(sK2),sK1))
    | ~ v1_relat_1(k6_relat_1(sK2)) ),
    inference(resolution,[],[f141,f166])).

fof(f166,plain,(
    r1_tarski(k6_relat_1(sK1),k6_relat_1(sK2)) ),
    inference(superposition,[],[f106,f165])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),X1)
      | r1_tarski(X0,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f135,f49])).

fof(f135,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k9_relat_1(X1,X0))
      | ~ r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f67,f111])).

fof(f111,plain,(
    ! [X1] : k9_relat_1(k6_relat_1(X1),X1) = X1 ),
    inference(forward_demodulation,[],[f110,f51])).

fof(f110,plain,(
    ! [X1] : k9_relat_1(k6_relat_1(X1),X1) = k2_relat_1(k6_relat_1(X1)) ),
    inference(subsumption_resolution,[],[f108,f49])).

fof(f108,plain,(
    ! [X1] :
      ( k9_relat_1(k6_relat_1(X1),X1) = k2_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f64,f84])).

fof(f84,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(subsumption_resolution,[],[f81,f49])).

fof(f81,plain,(
    ! [X0] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f52,f50])).

fof(f52,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f320,plain,(
    ! [X35,X36] : k9_relat_1(sK0,k9_relat_1(k6_relat_1(X35),X36)) = k9_relat_1(k7_relat_1(sK0,X35),X36) ),
    inference(resolution,[],[f158,f46])).

fof(f46,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f158,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_relat_1(X4)
      | k9_relat_1(X4,k9_relat_1(k6_relat_1(X3),X5)) = k9_relat_1(k7_relat_1(X4,X3),X5) ) ),
    inference(subsumption_resolution,[],[f155,f49])).

fof(f155,plain,(
    ! [X4,X5,X3] :
      ( k9_relat_1(X4,k9_relat_1(k6_relat_1(X3),X5)) = k9_relat_1(k7_relat_1(X4,X3),X5)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,(
    ! [X4,X5,X3] :
      ( k9_relat_1(X4,k9_relat_1(k6_relat_1(X3),X5)) = k9_relat_1(k7_relat_1(X4,X3),X5)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f66,f63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:01:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (1864)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.49  % (1856)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.49  % (1876)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.50  % (1868)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.50  % (1859)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (1880)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.52  % (1873)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.52  % (1854)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.52  % (1854)Refutation not found, incomplete strategy% (1854)------------------------------
% 0.19/0.52  % (1854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (1854)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (1854)Memory used [KB]: 1663
% 0.19/0.52  % (1854)Time elapsed: 0.115 s
% 0.19/0.52  % (1854)------------------------------
% 0.19/0.52  % (1854)------------------------------
% 0.19/0.52  % (1872)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.53  % (1881)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.53  % (1874)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.53  % (1855)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.53  % (1866)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.53  % (1857)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.53  % (1862)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.53  % (1870)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.53  % (1861)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.53  % (1878)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.54  % (1865)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.54  % (1858)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.54  % (1853)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.54  % (1883)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.54  % (1875)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.54  % (1877)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.54  % (1867)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.55  % (1860)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.55  % (1871)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.55  % (1882)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.56  % (1879)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.56  % (1869)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.60  % (1856)Refutation not found, incomplete strategy% (1856)------------------------------
% 0.19/0.60  % (1856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.62  % (1856)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.62  
% 1.82/0.62  % (1856)Memory used [KB]: 6140
% 1.82/0.62  % (1856)Time elapsed: 0.193 s
% 1.82/0.62  % (1856)------------------------------
% 1.82/0.62  % (1856)------------------------------
% 2.22/0.69  % (1892)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.73/0.73  % (1933)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.14/0.80  % (1855)Time limit reached!
% 3.14/0.80  % (1855)------------------------------
% 3.14/0.80  % (1855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.14/0.80  % (1878)Time limit reached!
% 3.14/0.80  % (1878)------------------------------
% 3.14/0.80  % (1878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.14/0.80  % (1878)Termination reason: Time limit
% 3.14/0.80  % (1878)Termination phase: Saturation
% 3.14/0.80  
% 3.14/0.80  % (1878)Memory used [KB]: 12792
% 3.14/0.80  % (1878)Time elapsed: 0.400 s
% 3.14/0.80  % (1878)------------------------------
% 3.14/0.80  % (1878)------------------------------
% 3.14/0.80  % (1855)Termination reason: Time limit
% 3.14/0.80  % (1855)Termination phase: Saturation
% 3.14/0.80  
% 3.14/0.80  % (1855)Memory used [KB]: 7931
% 3.14/0.80  % (1855)Time elapsed: 0.400 s
% 3.14/0.80  % (1855)------------------------------
% 3.14/0.80  % (1855)------------------------------
% 4.02/0.89  % (1859)Time limit reached!
% 4.02/0.89  % (1859)------------------------------
% 4.02/0.89  % (1859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.02/0.89  % (1859)Termination reason: Time limit
% 4.02/0.89  
% 4.02/0.89  % (1859)Memory used [KB]: 15607
% 4.02/0.89  % (1859)Time elapsed: 0.505 s
% 4.02/0.89  % (1859)------------------------------
% 4.02/0.89  % (1859)------------------------------
% 4.02/0.90  % (1883)Time limit reached!
% 4.02/0.90  % (1883)------------------------------
% 4.02/0.90  % (1883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.02/0.90  % (1883)Termination reason: Time limit
% 4.02/0.90  % (1883)Termination phase: Saturation
% 4.02/0.90  
% 4.02/0.90  % (1883)Memory used [KB]: 2302
% 4.02/0.90  % (1883)Time elapsed: 0.500 s
% 4.02/0.90  % (1883)------------------------------
% 4.02/0.90  % (1883)------------------------------
% 4.02/0.92  % (1868)Time limit reached!
% 4.02/0.92  % (1868)------------------------------
% 4.02/0.92  % (1868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.02/0.92  % (2034)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.34/0.93  % (1868)Termination reason: Time limit
% 4.34/0.93  
% 4.34/0.93  % (1868)Memory used [KB]: 6140
% 4.34/0.93  % (1868)Time elapsed: 0.521 s
% 4.34/0.93  % (1868)------------------------------
% 4.34/0.93  % (1868)------------------------------
% 4.34/0.93  % (2033)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.34/0.93  % (2033)Refutation not found, incomplete strategy% (2033)------------------------------
% 4.34/0.93  % (2033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/0.93  % (2033)Termination reason: Refutation not found, incomplete strategy
% 4.34/0.93  
% 4.34/0.93  % (2033)Memory used [KB]: 6268
% 4.34/0.93  % (2033)Time elapsed: 0.116 s
% 4.34/0.93  % (2033)------------------------------
% 4.34/0.93  % (2033)------------------------------
% 4.47/0.97  % (1876)Refutation found. Thanks to Tanya!
% 4.47/0.97  % SZS status Theorem for theBenchmark
% 4.47/0.97  % SZS output start Proof for theBenchmark
% 4.47/0.97  fof(f2847,plain,(
% 4.47/0.97    $false),
% 4.47/0.97    inference(subsumption_resolution,[],[f2843,f48])).
% 4.47/0.97  fof(f48,plain,(
% 4.47/0.97    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)),
% 4.47/0.97    inference(cnf_transformation,[],[f43])).
% 4.47/0.97  fof(f43,plain,(
% 4.47/0.97    (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2)) & v1_relat_1(sK0)),
% 4.47/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f42,f41])).
% 4.47/0.97  fof(f41,plain,(
% 4.47/0.97    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0)) => (? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) & v1_relat_1(sK0))),
% 4.47/0.97    introduced(choice_axiom,[])).
% 4.47/0.97  fof(f42,plain,(
% 4.47/0.97    ? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) => (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2))),
% 4.47/0.97    introduced(choice_axiom,[])).
% 4.47/0.97  fof(f24,plain,(
% 4.47/0.97    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0))),
% 4.47/0.97    inference(ennf_transformation,[],[f23])).
% 4.47/0.97  fof(f23,negated_conjecture,(
% 4.47/0.97    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 4.47/0.97    inference(negated_conjecture,[],[f22])).
% 4.47/0.97  fof(f22,conjecture,(
% 4.47/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 4.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 4.47/0.97  fof(f2843,plain,(
% 4.47/0.97    k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1)),
% 4.47/0.97    inference(superposition,[],[f320,f2785])).
% 4.47/0.97  fof(f2785,plain,(
% 4.47/0.97    sK1 = k9_relat_1(k6_relat_1(sK2),sK1)),
% 4.47/0.97    inference(resolution,[],[f2782,f309])).
% 4.47/0.97  fof(f309,plain,(
% 4.47/0.97    ( ! [X3] : (~r1_tarski(sK1,k9_relat_1(k6_relat_1(X3),sK1)) | sK1 = k9_relat_1(k6_relat_1(X3),sK1)) )),
% 4.47/0.97    inference(resolution,[],[f303,f71])).
% 4.47/0.97  fof(f71,plain,(
% 4.47/0.97    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 4.47/0.97    inference(cnf_transformation,[],[f45])).
% 4.47/0.97  fof(f45,plain,(
% 4.47/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.47/0.97    inference(flattening,[],[f44])).
% 4.47/0.97  fof(f44,plain,(
% 4.47/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.47/0.97    inference(nnf_transformation,[],[f1])).
% 4.47/0.97  fof(f1,axiom,(
% 4.47/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.47/0.97  fof(f303,plain,(
% 4.47/0.97    ( ! [X0] : (r1_tarski(k9_relat_1(k6_relat_1(X0),sK1),sK1)) )),
% 4.47/0.97    inference(backward_demodulation,[],[f281,f302])).
% 4.47/0.97  fof(f302,plain,(
% 4.47/0.97    ( ! [X7] : (k9_relat_1(k6_relat_1(X7),sK1) = k9_relat_1(k7_relat_1(k6_relat_1(X7),sK1),sK2)) )),
% 4.47/0.97    inference(forward_demodulation,[],[f301,f104])).
% 4.47/0.97  fof(f104,plain,(
% 4.47/0.97    ( ! [X2,X3] : (k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2)) )),
% 4.47/0.97    inference(subsumption_resolution,[],[f103,f49])).
% 4.47/0.97  fof(f49,plain,(
% 4.47/0.97    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 4.47/0.97    inference(cnf_transformation,[],[f9])).
% 4.47/0.97  fof(f9,axiom,(
% 4.47/0.97    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 4.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 4.47/0.97  fof(f103,plain,(
% 4.47/0.97    ( ! [X2,X3] : (k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2) | ~v1_relat_1(k6_relat_1(X2))) )),
% 4.47/0.97    inference(subsumption_resolution,[],[f101,f49])).
% 4.47/0.97  fof(f101,plain,(
% 4.47/0.97    ( ! [X2,X3] : (k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 4.47/0.97    inference(superposition,[],[f63,f62])).
% 4.47/0.97  fof(f62,plain,(
% 4.47/0.97    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 4.47/0.97    inference(cnf_transformation,[],[f30])).
% 4.47/0.97  fof(f30,plain,(
% 4.47/0.97    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 4.47/0.97    inference(ennf_transformation,[],[f13])).
% 4.47/0.97  fof(f13,axiom,(
% 4.47/0.97    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 4.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 4.47/0.97  fof(f63,plain,(
% 4.47/0.97    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 4.47/0.97    inference(cnf_transformation,[],[f31])).
% 4.47/0.97  fof(f31,plain,(
% 4.47/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 4.47/0.97    inference(ennf_transformation,[],[f19])).
% 4.47/0.97  fof(f19,axiom,(
% 4.47/0.97    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 4.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 4.47/0.97  fof(f301,plain,(
% 4.47/0.97    ( ! [X7] : (k9_relat_1(k8_relat_1(X7,k6_relat_1(sK1)),sK2) = k9_relat_1(k6_relat_1(X7),sK1)) )),
% 4.47/0.97    inference(subsumption_resolution,[],[f287,f49])).
% 4.47/0.97  fof(f287,plain,(
% 4.47/0.97    ( ! [X7] : (k9_relat_1(k8_relat_1(X7,k6_relat_1(sK1)),sK2) = k9_relat_1(k6_relat_1(X7),sK1) | ~v1_relat_1(k6_relat_1(sK1))) )),
% 4.47/0.97    inference(superposition,[],[f157,f171])).
% 4.47/0.97  fof(f171,plain,(
% 4.47/0.97    sK1 = k9_relat_1(k6_relat_1(sK1),sK2)),
% 4.47/0.97    inference(forward_demodulation,[],[f170,f51])).
% 4.47/0.97  fof(f51,plain,(
% 4.47/0.97    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 4.47/0.97    inference(cnf_transformation,[],[f17])).
% 4.47/0.97  fof(f17,axiom,(
% 4.47/0.97    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 4.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 4.47/0.97  fof(f170,plain,(
% 4.47/0.97    k9_relat_1(k6_relat_1(sK1),sK2) = k2_relat_1(k6_relat_1(sK1))),
% 4.47/0.97    inference(subsumption_resolution,[],[f167,f49])).
% 4.47/0.97  fof(f167,plain,(
% 4.47/0.97    k9_relat_1(k6_relat_1(sK1),sK2) = k2_relat_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1))),
% 4.47/0.97    inference(superposition,[],[f64,f165])).
% 4.47/0.97  fof(f165,plain,(
% 4.47/0.97    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK1),sK2)),
% 4.47/0.97    inference(resolution,[],[f130,f47])).
% 4.47/0.97  fof(f47,plain,(
% 4.47/0.97    r1_tarski(sK1,sK2)),
% 4.47/0.97    inference(cnf_transformation,[],[f43])).
% 4.47/0.97  fof(f130,plain,(
% 4.47/0.97    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 4.47/0.97    inference(subsumption_resolution,[],[f128,f49])).
% 4.47/0.97  fof(f128,plain,(
% 4.47/0.97    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 4.47/0.97    inference(superposition,[],[f65,f50])).
% 4.47/0.97  fof(f50,plain,(
% 4.47/0.97    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 4.47/0.97    inference(cnf_transformation,[],[f17])).
% 4.47/0.97  fof(f65,plain,(
% 4.47/0.97    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 4.47/0.97    inference(cnf_transformation,[],[f34])).
% 4.47/0.97  fof(f34,plain,(
% 4.47/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 4.47/0.97    inference(flattening,[],[f33])).
% 4.47/0.97  fof(f33,plain,(
% 4.47/0.97    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.47/0.97    inference(ennf_transformation,[],[f20])).
% 4.47/0.97  fof(f20,axiom,(
% 4.47/0.97    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 4.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 4.47/0.97  fof(f64,plain,(
% 4.47/0.97    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.47/0.97    inference(cnf_transformation,[],[f32])).
% 4.47/0.97  fof(f32,plain,(
% 4.47/0.97    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.47/0.97    inference(ennf_transformation,[],[f14])).
% 4.47/0.97  fof(f14,axiom,(
% 4.47/0.97    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 4.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 4.47/0.97  fof(f157,plain,(
% 4.47/0.97    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) = k9_relat_1(k8_relat_1(X1,X0),X2) | ~v1_relat_1(X0)) )),
% 4.47/0.97    inference(subsumption_resolution,[],[f156,f49])).
% 4.47/0.97  fof(f156,plain,(
% 4.47/0.97    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) = k9_relat_1(k8_relat_1(X1,X0),X2) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 4.47/0.97    inference(duplicate_literal_removal,[],[f149])).
% 4.47/0.97  fof(f149,plain,(
% 4.47/0.97    ( ! [X2,X0,X1] : (k9_relat_1(k6_relat_1(X1),k9_relat_1(X0,X2)) = k9_relat_1(k8_relat_1(X1,X0),X2) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.47/0.97    inference(superposition,[],[f66,f62])).
% 4.47/0.97  fof(f66,plain,(
% 4.47/0.97    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 4.47/0.97    inference(cnf_transformation,[],[f35])).
% 4.47/0.97  fof(f35,plain,(
% 4.47/0.97    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 4.47/0.97    inference(ennf_transformation,[],[f16])).
% 4.47/0.97  fof(f16,axiom,(
% 4.47/0.97    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 4.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).
% 4.47/0.97  fof(f281,plain,(
% 4.47/0.97    ( ! [X0] : (r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X0),sK1),sK2),sK1)) )),
% 4.47/0.97    inference(subsumption_resolution,[],[f278,f49])).
% 4.47/0.97  fof(f278,plain,(
% 4.47/0.97    ( ! [X0] : (r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X0),sK1),sK2),sK1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 4.47/0.97    inference(resolution,[],[f240,f59])).
% 4.47/0.97  fof(f59,plain,(
% 4.47/0.97    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 4.47/0.97    inference(cnf_transformation,[],[f27])).
% 4.47/0.97  fof(f27,plain,(
% 4.47/0.97    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 4.47/0.97    inference(ennf_transformation,[],[f10])).
% 4.47/0.97  fof(f10,axiom,(
% 4.47/0.97    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 4.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 4.47/0.97  fof(f240,plain,(
% 4.47/0.97    ( ! [X2] : (~v1_relat_1(k7_relat_1(k6_relat_1(X2),sK1)) | r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X2),sK1),sK2),sK1)) )),
% 4.47/0.97    inference(resolution,[],[f195,f106])).
% 4.47/0.97  fof(f106,plain,(
% 4.47/0.97    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1))) )),
% 4.47/0.97    inference(subsumption_resolution,[],[f105,f49])).
% 4.47/0.97  fof(f105,plain,(
% 4.47/0.97    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 4.47/0.97    inference(superposition,[],[f60,f104])).
% 4.47/0.97  fof(f60,plain,(
% 4.47/0.97    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 4.47/0.97    inference(cnf_transformation,[],[f28])).
% 4.47/0.97  fof(f28,plain,(
% 4.47/0.97    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 4.47/0.97    inference(ennf_transformation,[],[f12])).
% 4.47/0.97  fof(f12,axiom,(
% 4.47/0.97    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 4.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).
% 4.47/0.97  fof(f195,plain,(
% 4.47/0.97    ( ! [X0] : (~r1_tarski(X0,k6_relat_1(sK1)) | r1_tarski(k9_relat_1(X0,sK2),sK1) | ~v1_relat_1(X0)) )),
% 4.47/0.97    inference(subsumption_resolution,[],[f193,f49])).
% 4.47/0.97  fof(f193,plain,(
% 4.47/0.97    ( ! [X0] : (r1_tarski(k9_relat_1(X0,sK2),sK1) | ~r1_tarski(X0,k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1)) | ~v1_relat_1(X0)) )),
% 4.47/0.97    inference(superposition,[],[f67,f171])).
% 4.47/0.97  fof(f67,plain,(
% 4.47/0.97    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 4.47/0.97    inference(cnf_transformation,[],[f37])).
% 4.47/0.97  fof(f37,plain,(
% 4.47/0.97    ! [X0,X1] : (! [X2] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 4.47/0.97    inference(flattening,[],[f36])).
% 4.47/0.97  fof(f36,plain,(
% 4.47/0.97    ! [X0,X1] : (! [X2] : ((r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 4.47/0.97    inference(ennf_transformation,[],[f15])).
% 4.47/0.97  fof(f15,axiom,(
% 4.47/0.97    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 4.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).
% 4.47/0.97  fof(f2782,plain,(
% 4.47/0.97    r1_tarski(sK1,k9_relat_1(k6_relat_1(sK2),sK1))),
% 4.47/0.97    inference(subsumption_resolution,[],[f2770,f49])).
% 4.47/0.97  fof(f2770,plain,(
% 4.47/0.97    r1_tarski(sK1,k9_relat_1(k6_relat_1(sK2),sK1)) | ~v1_relat_1(k6_relat_1(sK2))),
% 4.47/0.97    inference(resolution,[],[f141,f166])).
% 4.47/0.97  fof(f166,plain,(
% 4.47/0.97    r1_tarski(k6_relat_1(sK1),k6_relat_1(sK2))),
% 4.47/0.97    inference(superposition,[],[f106,f165])).
% 4.47/0.97  fof(f141,plain,(
% 4.47/0.97    ( ! [X0,X1] : (~r1_tarski(k6_relat_1(X0),X1) | r1_tarski(X0,k9_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 4.47/0.97    inference(subsumption_resolution,[],[f135,f49])).
% 4.47/0.97  fof(f135,plain,(
% 4.47/0.97    ( ! [X0,X1] : (r1_tarski(X0,k9_relat_1(X1,X0)) | ~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 4.47/0.97    inference(superposition,[],[f67,f111])).
% 4.47/0.97  fof(f111,plain,(
% 4.47/0.97    ( ! [X1] : (k9_relat_1(k6_relat_1(X1),X1) = X1) )),
% 4.47/0.97    inference(forward_demodulation,[],[f110,f51])).
% 4.47/0.97  fof(f110,plain,(
% 4.47/0.97    ( ! [X1] : (k9_relat_1(k6_relat_1(X1),X1) = k2_relat_1(k6_relat_1(X1))) )),
% 4.47/0.97    inference(subsumption_resolution,[],[f108,f49])).
% 4.47/0.97  fof(f108,plain,(
% 4.47/0.97    ( ! [X1] : (k9_relat_1(k6_relat_1(X1),X1) = k2_relat_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 4.47/0.97    inference(superposition,[],[f64,f84])).
% 4.47/0.97  fof(f84,plain,(
% 4.47/0.97    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 4.47/0.97    inference(subsumption_resolution,[],[f81,f49])).
% 4.47/0.97  fof(f81,plain,(
% 4.47/0.97    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 4.47/0.97    inference(superposition,[],[f52,f50])).
% 4.47/0.97  fof(f52,plain,(
% 4.47/0.97    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 4.47/0.97    inference(cnf_transformation,[],[f25])).
% 4.47/0.97  fof(f25,plain,(
% 4.47/0.97    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 4.47/0.97    inference(ennf_transformation,[],[f21])).
% 4.47/0.97  fof(f21,axiom,(
% 4.47/0.97    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 4.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 4.47/0.97  fof(f320,plain,(
% 4.47/0.97    ( ! [X35,X36] : (k9_relat_1(sK0,k9_relat_1(k6_relat_1(X35),X36)) = k9_relat_1(k7_relat_1(sK0,X35),X36)) )),
% 4.47/0.97    inference(resolution,[],[f158,f46])).
% 4.47/0.97  fof(f46,plain,(
% 4.47/0.97    v1_relat_1(sK0)),
% 4.47/0.97    inference(cnf_transformation,[],[f43])).
% 4.47/0.97  fof(f158,plain,(
% 4.47/0.97    ( ! [X4,X5,X3] : (~v1_relat_1(X4) | k9_relat_1(X4,k9_relat_1(k6_relat_1(X3),X5)) = k9_relat_1(k7_relat_1(X4,X3),X5)) )),
% 4.47/0.97    inference(subsumption_resolution,[],[f155,f49])).
% 4.47/0.97  fof(f155,plain,(
% 4.47/0.97    ( ! [X4,X5,X3] : (k9_relat_1(X4,k9_relat_1(k6_relat_1(X3),X5)) = k9_relat_1(k7_relat_1(X4,X3),X5) | ~v1_relat_1(X4) | ~v1_relat_1(k6_relat_1(X3))) )),
% 4.47/0.97    inference(duplicate_literal_removal,[],[f150])).
% 4.47/0.97  fof(f150,plain,(
% 4.47/0.97    ( ! [X4,X5,X3] : (k9_relat_1(X4,k9_relat_1(k6_relat_1(X3),X5)) = k9_relat_1(k7_relat_1(X4,X3),X5) | ~v1_relat_1(X4) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(X4)) )),
% 4.47/0.97    inference(superposition,[],[f66,f63])).
% 4.47/0.97  % SZS output end Proof for theBenchmark
% 4.47/0.97  % (1876)------------------------------
% 4.47/0.97  % (1876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.47/0.97  % (1876)Termination reason: Refutation
% 4.47/0.97  
% 4.47/0.97  % (1876)Memory used [KB]: 11641
% 4.47/0.97  % (1876)Time elapsed: 0.557 s
% 4.47/0.97  % (1876)------------------------------
% 4.47/0.97  % (1876)------------------------------
% 4.47/0.98  % (1852)Success in time 0.614 s
%------------------------------------------------------------------------------
