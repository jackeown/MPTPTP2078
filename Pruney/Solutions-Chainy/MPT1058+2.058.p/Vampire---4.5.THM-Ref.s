%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:25 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 278 expanded)
%              Number of leaves         :   17 (  77 expanded)
%              Depth                    :   21
%              Number of atoms          :  248 ( 681 expanded)
%              Number of equality atoms :   53 ( 190 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f559,plain,(
    $false ),
    inference(subsumption_resolution,[],[f558,f42])).

fof(f42,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(f558,plain,(
    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(forward_demodulation,[],[f557,f292])).

fof(f292,plain,(
    ! [X2] : k9_relat_1(k6_relat_1(X2),X2) = X2 ),
    inference(subsumption_resolution,[],[f290,f119])).

fof(f119,plain,(
    ! [X0] : r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X0) ),
    inference(subsumption_resolution,[],[f118,f43])).

fof(f43,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f118,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f115,f44])).

fof(f44,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f115,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X0)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f52,f71])).

fof(f71,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f70,f45])).

fof(f45,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f70,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f69,f46])).

fof(f46,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f47,f43])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f290,plain,(
    ! [X2] :
      ( k9_relat_1(k6_relat_1(X2),X2) = X2
      | ~ r1_tarski(k9_relat_1(k6_relat_1(X2),X2),X2) ) ),
    inference(resolution,[],[f287,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f287,plain,(
    ! [X0] : r1_tarski(X0,k9_relat_1(k6_relat_1(X0),X0)) ),
    inference(subsumption_resolution,[],[f286,f64])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f286,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,X0)
      | r1_tarski(X0,k9_relat_1(k6_relat_1(X0),X0)) ) ),
    inference(forward_demodulation,[],[f285,f45])).

fof(f285,plain,(
    ! [X0] :
      ( r1_tarski(X0,k9_relat_1(k6_relat_1(X0),X0))
      | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) ) ),
    inference(subsumption_resolution,[],[f282,f43])).

fof(f282,plain,(
    ! [X0] :
      ( r1_tarski(X0,k9_relat_1(k6_relat_1(X0),X0))
      | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f224,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f224,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2))
      | r1_tarski(X1,X2) ) ),
    inference(subsumption_resolution,[],[f223,f64])).

fof(f223,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X1)
      | ~ r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2))
      | r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f222,f46])).

fof(f222,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2))
      | ~ r1_tarski(X1,k2_relat_1(k6_relat_1(X1)))
      | r1_tarski(X1,X2) ) ),
    inference(subsumption_resolution,[],[f221,f43])).

fof(f221,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2))
      | ~ r1_tarski(X1,k2_relat_1(k6_relat_1(X1)))
      | r1_tarski(X1,X2)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f211,f44])).

fof(f211,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2))
      | ~ r1_tarski(X1,k2_relat_1(k6_relat_1(X1)))
      | r1_tarski(X1,X2)
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f59,f71])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_relat_1(X2))
      | ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(f557,plain,(
    k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f540,f154])).

fof(f154,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK0,X1))) ),
    inference(resolution,[],[f63,f39])).

fof(f39,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f57,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f540,plain,(
    k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) = k1_setfam_1(k1_enumset1(sK1,sK1,k10_relat_1(sK0,sK2))) ),
    inference(superposition,[],[f521,f189])).

fof(f189,plain,(
    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f188,f67])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f66,f43])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f50,f45])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f188,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)
    | ~ r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f185,f56])).

fof(f185,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) ),
    inference(subsumption_resolution,[],[f184,f64])).

fof(f184,plain,
    ( ~ r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2))
    | r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) ),
    inference(forward_demodulation,[],[f183,f45])).

fof(f183,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))) ),
    inference(subsumption_resolution,[],[f182,f43])).

fof(f182,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f171,f44])).

fof(f171,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))
    | ~ r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))))
    | ~ v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2)))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) ),
    inference(resolution,[],[f58,f133])).

fof(f133,plain,(
    r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1) ),
    inference(resolution,[],[f119,f103])).

fof(f103,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k10_relat_1(sK0,sK2))
      | r1_tarski(X2,sK1) ) ),
    inference(resolution,[],[f60,f41])).

fof(f41,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f521,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,X1)) ),
    inference(forward_demodulation,[],[f265,f292])).

fof(f265,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k6_relat_1(X1),X1))) ),
    inference(forward_demodulation,[],[f264,f45])).

fof(f264,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1))))) ),
    inference(subsumption_resolution,[],[f261,f43])).

fof(f261,plain,(
    ! [X2,X1] :
      ( k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1)))))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(resolution,[],[f62,f44])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1))))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f53,f61])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:44:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (16741)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (16751)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (16759)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (16746)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (16749)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (16744)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (16739)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (16762)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (16754)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (16743)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (16740)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (16760)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (16768)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.36/0.53  % (16753)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.36/0.54  % (16742)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.36/0.54  % (16756)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.36/0.54  % (16745)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.54  % (16748)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.36/0.54  % (16767)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.36/0.54  % (16761)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.36/0.54  % (16747)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.36/0.54  % (16752)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.36/0.54  % (16766)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.36/0.55  % (16755)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.36/0.55  % (16763)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.36/0.55  % (16750)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.36/0.55  % (16758)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.51/0.55  % (16765)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.51/0.55  % (16764)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.51/0.56  % (16757)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.51/0.57  % (16745)Refutation found. Thanks to Tanya!
% 1.51/0.57  % SZS status Theorem for theBenchmark
% 1.51/0.57  % SZS output start Proof for theBenchmark
% 1.51/0.57  fof(f559,plain,(
% 1.51/0.57    $false),
% 1.51/0.57    inference(subsumption_resolution,[],[f558,f42])).
% 1.51/0.57  fof(f42,plain,(
% 1.51/0.57    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.51/0.57    inference(cnf_transformation,[],[f36])).
% 1.51/0.57  fof(f36,plain,(
% 1.51/0.57    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.51/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f35,f34])).
% 1.51/0.57  fof(f34,plain,(
% 1.51/0.57    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.51/0.57    introduced(choice_axiom,[])).
% 1.51/0.57  fof(f35,plain,(
% 1.51/0.57    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 1.51/0.57    introduced(choice_axiom,[])).
% 1.51/0.57  fof(f18,plain,(
% 1.51/0.57    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.51/0.57    inference(flattening,[],[f17])).
% 1.51/0.57  fof(f17,plain,(
% 1.51/0.57    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f16])).
% 1.51/0.57  fof(f16,negated_conjecture,(
% 1.51/0.57    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.51/0.57    inference(negated_conjecture,[],[f15])).
% 1.51/0.57  fof(f15,conjecture,(
% 1.51/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).
% 1.51/0.57  fof(f558,plain,(
% 1.51/0.57    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.51/0.57    inference(forward_demodulation,[],[f557,f292])).
% 1.51/0.57  fof(f292,plain,(
% 1.51/0.57    ( ! [X2] : (k9_relat_1(k6_relat_1(X2),X2) = X2) )),
% 1.51/0.57    inference(subsumption_resolution,[],[f290,f119])).
% 1.51/0.57  fof(f119,plain,(
% 1.51/0.57    ( ! [X0] : (r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X0)) )),
% 1.51/0.57    inference(subsumption_resolution,[],[f118,f43])).
% 1.51/0.57  fof(f43,plain,(
% 1.51/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f8])).
% 1.51/0.57  fof(f8,axiom,(
% 1.51/0.57    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.51/0.57  fof(f118,plain,(
% 1.51/0.57    ( ! [X0] : (r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.51/0.57    inference(subsumption_resolution,[],[f115,f44])).
% 1.51/0.57  fof(f44,plain,(
% 1.51/0.57    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f8])).
% 1.51/0.57  fof(f115,plain,(
% 1.51/0.57    ( ! [X0] : (r1_tarski(k9_relat_1(k6_relat_1(X0),X0),X0) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.51/0.57    inference(superposition,[],[f52,f71])).
% 1.51/0.57  fof(f71,plain,(
% 1.51/0.57    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 1.51/0.57    inference(forward_demodulation,[],[f70,f45])).
% 1.51/0.57  fof(f45,plain,(
% 1.51/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.51/0.57    inference(cnf_transformation,[],[f7])).
% 1.51/0.57  fof(f7,axiom,(
% 1.51/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.51/0.57  fof(f70,plain,(
% 1.51/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)) )),
% 1.51/0.57    inference(forward_demodulation,[],[f69,f46])).
% 1.51/0.57  fof(f46,plain,(
% 1.51/0.57    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.51/0.57    inference(cnf_transformation,[],[f7])).
% 1.51/0.57  fof(f69,plain,(
% 1.51/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0)))) )),
% 1.51/0.57    inference(resolution,[],[f47,f43])).
% 1.51/0.57  fof(f47,plain,(
% 1.51/0.57    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f19])).
% 1.51/0.57  fof(f19,plain,(
% 1.51/0.57    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.51/0.57    inference(ennf_transformation,[],[f6])).
% 1.51/0.57  fof(f6,axiom,(
% 1.51/0.57    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.51/0.57  fof(f52,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f24])).
% 1.51/0.57  fof(f24,plain,(
% 1.51/0.57    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.51/0.57    inference(flattening,[],[f23])).
% 1.51/0.57  fof(f23,plain,(
% 1.51/0.57    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.51/0.57    inference(ennf_transformation,[],[f10])).
% 1.51/0.57  fof(f10,axiom,(
% 1.51/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 1.51/0.57  fof(f290,plain,(
% 1.51/0.57    ( ! [X2] : (k9_relat_1(k6_relat_1(X2),X2) = X2 | ~r1_tarski(k9_relat_1(k6_relat_1(X2),X2),X2)) )),
% 1.51/0.57    inference(resolution,[],[f287,f56])).
% 1.51/0.57  fof(f56,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f38])).
% 1.51/0.57  fof(f38,plain,(
% 1.51/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.51/0.57    inference(flattening,[],[f37])).
% 1.51/0.57  fof(f37,plain,(
% 1.51/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.51/0.57    inference(nnf_transformation,[],[f1])).
% 1.51/0.57  fof(f1,axiom,(
% 1.51/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.51/0.57  fof(f287,plain,(
% 1.51/0.57    ( ! [X0] : (r1_tarski(X0,k9_relat_1(k6_relat_1(X0),X0))) )),
% 1.51/0.57    inference(subsumption_resolution,[],[f286,f64])).
% 1.51/0.57  fof(f64,plain,(
% 1.51/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.51/0.57    inference(equality_resolution,[],[f55])).
% 1.51/0.57  fof(f55,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.51/0.57    inference(cnf_transformation,[],[f38])).
% 1.51/0.57  fof(f286,plain,(
% 1.51/0.57    ( ! [X0] : (~r1_tarski(X0,X0) | r1_tarski(X0,k9_relat_1(k6_relat_1(X0),X0))) )),
% 1.51/0.57    inference(forward_demodulation,[],[f285,f45])).
% 1.51/0.57  fof(f285,plain,(
% 1.51/0.57    ( ! [X0] : (r1_tarski(X0,k9_relat_1(k6_relat_1(X0),X0)) | ~r1_tarski(X0,k1_relat_1(k6_relat_1(X0)))) )),
% 1.51/0.57    inference(subsumption_resolution,[],[f282,f43])).
% 1.51/0.57  fof(f282,plain,(
% 1.51/0.57    ( ! [X0] : (r1_tarski(X0,k9_relat_1(k6_relat_1(X0),X0)) | ~r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.51/0.57    inference(resolution,[],[f224,f51])).
% 1.51/0.57  fof(f51,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f22])).
% 1.51/0.57  fof(f22,plain,(
% 1.51/0.57    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.51/0.57    inference(flattening,[],[f21])).
% 1.51/0.57  fof(f21,plain,(
% 1.51/0.57    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.51/0.57    inference(ennf_transformation,[],[f11])).
% 1.51/0.57  fof(f11,axiom,(
% 1.51/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.51/0.57  fof(f224,plain,(
% 1.51/0.57    ( ! [X2,X1] : (~r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2)) | r1_tarski(X1,X2)) )),
% 1.51/0.57    inference(subsumption_resolution,[],[f223,f64])).
% 1.51/0.57  fof(f223,plain,(
% 1.51/0.57    ( ! [X2,X1] : (~r1_tarski(X1,X1) | ~r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2)) | r1_tarski(X1,X2)) )),
% 1.51/0.57    inference(forward_demodulation,[],[f222,f46])).
% 1.51/0.57  fof(f222,plain,(
% 1.51/0.57    ( ! [X2,X1] : (~r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2)) | ~r1_tarski(X1,k2_relat_1(k6_relat_1(X1))) | r1_tarski(X1,X2)) )),
% 1.51/0.57    inference(subsumption_resolution,[],[f221,f43])).
% 1.51/0.57  fof(f221,plain,(
% 1.51/0.57    ( ! [X2,X1] : (~r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2)) | ~r1_tarski(X1,k2_relat_1(k6_relat_1(X1))) | r1_tarski(X1,X2) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.51/0.57    inference(subsumption_resolution,[],[f211,f44])).
% 1.51/0.57  fof(f211,plain,(
% 1.51/0.57    ( ! [X2,X1] : (~r1_tarski(X1,k10_relat_1(k6_relat_1(X1),X2)) | ~r1_tarski(X1,k2_relat_1(k6_relat_1(X1))) | r1_tarski(X1,X2) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.51/0.57    inference(superposition,[],[f59,f71])).
% 1.51/0.57  fof(f59,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,k2_relat_1(X2)) | r1_tarski(X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f31])).
% 1.51/0.57  fof(f31,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k2_relat_1(X2)) | ~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.51/0.57    inference(flattening,[],[f30])).
% 1.51/0.57  fof(f30,plain,(
% 1.51/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~r1_tarski(X0,k2_relat_1(X2)) | ~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.51/0.57    inference(ennf_transformation,[],[f13])).
% 1.51/0.57  fof(f13,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).
% 1.51/0.57  fof(f557,plain,(
% 1.51/0.57    k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2))),
% 1.51/0.57    inference(forward_demodulation,[],[f540,f154])).
% 1.51/0.57  fof(f154,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK0,X1)))) )),
% 1.51/0.57    inference(resolution,[],[f63,f39])).
% 1.51/0.57  fof(f39,plain,(
% 1.51/0.57    v1_relat_1(sK0)),
% 1.51/0.57    inference(cnf_transformation,[],[f36])).
% 1.51/0.57  fof(f63,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1)))) )),
% 1.51/0.57    inference(definition_unfolding,[],[f57,f61])).
% 1.51/0.57  fof(f61,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.51/0.57    inference(definition_unfolding,[],[f48,f49])).
% 1.51/0.57  fof(f49,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f3])).
% 1.51/0.57  fof(f3,axiom,(
% 1.51/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.51/0.57  fof(f48,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f4])).
% 1.51/0.57  fof(f4,axiom,(
% 1.51/0.57    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.51/0.57  fof(f57,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f27])).
% 1.51/0.57  fof(f27,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.51/0.57    inference(ennf_transformation,[],[f9])).
% 1.51/0.57  fof(f9,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 1.51/0.57  fof(f540,plain,(
% 1.51/0.57    k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)) = k1_setfam_1(k1_enumset1(sK1,sK1,k10_relat_1(sK0,sK2)))),
% 1.51/0.57    inference(superposition,[],[f521,f189])).
% 1.51/0.57  fof(f189,plain,(
% 1.51/0.57    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)),
% 1.51/0.57    inference(subsumption_resolution,[],[f188,f67])).
% 1.51/0.57  fof(f67,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 1.51/0.57    inference(subsumption_resolution,[],[f66,f43])).
% 1.51/0.57  fof(f66,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.51/0.57    inference(superposition,[],[f50,f45])).
% 1.51/0.57  fof(f50,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f20])).
% 1.51/0.57  fof(f20,plain,(
% 1.51/0.57    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.51/0.57    inference(ennf_transformation,[],[f5])).
% 1.51/0.57  fof(f5,axiom,(
% 1.51/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 1.51/0.57  fof(f188,plain,(
% 1.51/0.57    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) | ~r1_tarski(k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),k10_relat_1(sK0,sK2))),
% 1.51/0.57    inference(resolution,[],[f185,f56])).
% 1.51/0.57  fof(f185,plain,(
% 1.51/0.57    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))),
% 1.51/0.57    inference(subsumption_resolution,[],[f184,f64])).
% 1.51/0.57  fof(f184,plain,(
% 1.51/0.57    ~r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK2)) | r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1))),
% 1.51/0.57    inference(forward_demodulation,[],[f183,f45])).
% 1.51/0.57  fof(f183,plain,(
% 1.51/0.57    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))))),
% 1.51/0.57    inference(subsumption_resolution,[],[f182,f43])).
% 1.51/0.57  fof(f182,plain,(
% 1.51/0.57    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))) | ~v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))),
% 1.51/0.57    inference(subsumption_resolution,[],[f171,f44])).
% 1.51/0.57  fof(f171,plain,(
% 1.51/0.57    r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)) | ~r1_tarski(k10_relat_1(sK0,sK2),k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))) | ~v1_funct_1(k6_relat_1(k10_relat_1(sK0,sK2))) | ~v1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))),
% 1.51/0.57    inference(resolution,[],[f58,f133])).
% 1.51/0.57  fof(f133,plain,(
% 1.51/0.57    r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),k10_relat_1(sK0,sK2)),sK1)),
% 1.51/0.57    inference(resolution,[],[f119,f103])).
% 1.51/0.57  fof(f103,plain,(
% 1.51/0.57    ( ! [X2] : (~r1_tarski(X2,k10_relat_1(sK0,sK2)) | r1_tarski(X2,sK1)) )),
% 1.51/0.57    inference(resolution,[],[f60,f41])).
% 1.51/0.57  fof(f41,plain,(
% 1.51/0.57    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.51/0.57    inference(cnf_transformation,[],[f36])).
% 1.51/0.57  fof(f60,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f33])).
% 1.51/0.57  fof(f33,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.51/0.57    inference(flattening,[],[f32])).
% 1.51/0.57  fof(f32,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.51/0.57    inference(ennf_transformation,[],[f2])).
% 1.51/0.57  fof(f2,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.51/0.57  fof(f58,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f29])).
% 1.51/0.57  fof(f29,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.51/0.57    inference(flattening,[],[f28])).
% 1.51/0.57  fof(f28,plain,(
% 1.51/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.51/0.57    inference(ennf_transformation,[],[f14])).
% 1.51/0.57  fof(f14,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 1.51/0.57  fof(f521,plain,(
% 1.51/0.57    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,X1))) )),
% 1.51/0.57    inference(forward_demodulation,[],[f265,f292])).
% 1.51/0.57  fof(f265,plain,(
% 1.51/0.57    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k6_relat_1(X1),X1)))) )),
% 1.51/0.57    inference(forward_demodulation,[],[f264,f45])).
% 1.51/0.57  fof(f264,plain,(
% 1.51/0.57    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1)))))) )),
% 1.51/0.57    inference(subsumption_resolution,[],[f261,f43])).
% 1.51/0.57  fof(f261,plain,(
% 1.51/0.57    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1))))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.51/0.57    inference(resolution,[],[f62,f44])).
% 1.51/0.59  fof(f62,plain,(
% 1.51/0.59    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) | ~v1_relat_1(X1)) )),
% 1.51/0.59    inference(definition_unfolding,[],[f53,f61])).
% 1.51/0.59  fof(f53,plain,(
% 1.51/0.59    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f26])).
% 1.51/0.59  fof(f26,plain,(
% 1.51/0.59    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.51/0.59    inference(flattening,[],[f25])).
% 1.51/0.59  fof(f25,plain,(
% 1.51/0.59    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.51/0.59    inference(ennf_transformation,[],[f12])).
% 1.51/0.59  fof(f12,axiom,(
% 1.51/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 1.51/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 1.51/0.59  % SZS output end Proof for theBenchmark
% 1.51/0.59  % (16745)------------------------------
% 1.51/0.59  % (16745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.59  % (16745)Termination reason: Refutation
% 1.51/0.59  
% 1.51/0.59  % (16745)Memory used [KB]: 11001
% 1.51/0.59  % (16745)Time elapsed: 0.159 s
% 1.51/0.59  % (16745)------------------------------
% 1.51/0.59  % (16745)------------------------------
% 1.51/0.59  % (16737)Success in time 0.237 s
%------------------------------------------------------------------------------
