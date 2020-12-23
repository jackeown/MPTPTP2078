%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:50 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 319 expanded)
%              Number of leaves         :   22 (  87 expanded)
%              Depth                    :   21
%              Number of atoms          :  223 ( 699 expanded)
%              Number of equality atoms :   89 ( 199 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f423,plain,(
    $false ),
    inference(subsumption_resolution,[],[f422,f47])).

fof(f47,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f39])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f422,plain,(
    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f420,f117])).

fof(f117,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(subsumption_resolution,[],[f116,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f116,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f80,f79])).

fof(f79,plain,(
    ! [X0] : k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f55,f77])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f68,f78])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f58,f77])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f420,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(superposition,[],[f148,f410])).

fof(f410,plain,(
    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f409,f45])).

fof(f45,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f409,plain,
    ( sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f284,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f284,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f283,f266])).

fof(f266,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f263,f49])).

fof(f49,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f263,plain,(
    k1_relat_1(k7_relat_1(sK1,sK0)) = k1_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[],[f205,f257])).

fof(f257,plain,(
    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f156,f46])).

fof(f46,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f156,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(forward_demodulation,[],[f154,f49])).

fof(f154,plain,(
    ! [X2,X1] :
      ( k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)
      | ~ r1_tarski(k1_relat_1(k6_relat_1(X1)),X2) ) ),
    inference(resolution,[],[f100,f48])).

fof(f48,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = X0
      | ~ r1_tarski(k1_relat_1(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,X1) = X0
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f63,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f205,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f198,f144])).

fof(f144,plain,(
    ! [X2] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X2),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X2))) ),
    inference(subsumption_resolution,[],[f141,f48])).

fof(f141,plain,(
    ! [X2] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X2),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X2)))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f60,f131])).

fof(f131,plain,(
    ! [X0] : k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(forward_demodulation,[],[f129,f49])).

fof(f129,plain,(
    ! [X0] : k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,k1_relat_1(k6_relat_1(X0))))) ),
    inference(resolution,[],[f124,f48])).

fof(f124,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(sK1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(X0)))) ) ),
    inference(resolution,[],[f53,f45])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f198,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X0)))
      | k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))) ) ),
    inference(superposition,[],[f175,f181])).

fof(f181,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)))) ),
    inference(resolution,[],[f127,f45])).

fof(f127,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,k1_relat_1(k7_relat_1(k6_relat_1(X2),k1_relat_1(X1)))) = k7_relat_1(X1,X2) ) ),
    inference(forward_demodulation,[],[f125,f49])).

fof(f125,plain,(
    ! [X2,X1] :
      ( k7_relat_1(X1,k1_relat_1(k6_relat_1(X2))) = k7_relat_1(X1,k1_relat_1(k7_relat_1(k6_relat_1(X2),k1_relat_1(X1))))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f53,f48])).

fof(f175,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(k7_relat_1(sK1,X0)))
      | k1_relat_1(k7_relat_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f95,f45])).

fof(f95,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X1,k1_relat_1(k7_relat_1(X2,X1)))
      | k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ),
    inference(resolution,[],[f66,f60])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f283,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f51,f277])).

fof(f277,plain,(
    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f171,f266])).

fof(f171,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(resolution,[],[f110,f45])).

fof(f110,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X3)
      | k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4))) ) ),
    inference(subsumption_resolution,[],[f109,f59])).

fof(f109,plain,(
    ! [X4,X3] :
      ( k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k7_relat_1(X3,X4)) ) ),
    inference(subsumption_resolution,[],[f107,f60])).

fof(f107,plain,(
    ! [X4,X3] :
      ( k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(X3,X4)),X4)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k7_relat_1(X3,X4)) ) ),
    inference(superposition,[],[f54,f52])).

fof(f52,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(f51,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f148,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k5_xboole_0(X1,k10_relat_1(k7_relat_1(sK1,X1),X2))
      | r1_tarski(X1,k10_relat_1(sK1,X2)) ) ),
    inference(superposition,[],[f81,f132])).

fof(f132,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k10_relat_1(sK1,X1))) ),
    inference(resolution,[],[f82,f45])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f70,f77])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f78])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (22196)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (22211)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (22195)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.35/0.53  % (22189)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.35/0.53  % (22191)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.35/0.53  % (22190)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.35/0.54  % (22210)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.35/0.54  % (22212)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.35/0.54  % (22202)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.35/0.54  % (22214)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.35/0.54  % (22204)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.35/0.54  % (22188)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.35/0.54  % (22192)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.35/0.54  % (22199)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.35/0.55  % (22206)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.50/0.55  % (22197)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.50/0.55  % (22215)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.50/0.55  % (22205)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.50/0.55  % (22198)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.50/0.56  % (22209)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.50/0.56  % (22207)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.50/0.56  % (22217)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.50/0.56  % (22201)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.50/0.56  % (22216)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.50/0.56  % (22193)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.50/0.57  % (22213)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.50/0.57  % (22194)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.57  % (22200)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.50/0.58  % (22208)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.50/0.58  % (22203)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.50/0.60  % (22210)Refutation found. Thanks to Tanya!
% 1.50/0.60  % SZS status Theorem for theBenchmark
% 1.50/0.60  % SZS output start Proof for theBenchmark
% 1.50/0.60  fof(f423,plain,(
% 1.50/0.60    $false),
% 1.50/0.60    inference(subsumption_resolution,[],[f422,f47])).
% 1.50/0.60  fof(f47,plain,(
% 1.50/0.60    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.50/0.60    inference(cnf_transformation,[],[f40])).
% 1.50/0.60  fof(f40,plain,(
% 1.50/0.60    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.50/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f39])).
% 1.50/0.60  fof(f39,plain,(
% 1.50/0.60    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.50/0.60    introduced(choice_axiom,[])).
% 1.50/0.60  fof(f26,plain,(
% 1.50/0.60    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.50/0.60    inference(flattening,[],[f25])).
% 1.50/0.60  fof(f25,plain,(
% 1.50/0.60    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.50/0.60    inference(ennf_transformation,[],[f23])).
% 1.50/0.60  fof(f23,negated_conjecture,(
% 1.50/0.60    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.50/0.60    inference(negated_conjecture,[],[f22])).
% 1.50/0.60  fof(f22,conjecture,(
% 1.50/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 1.50/0.60  fof(f422,plain,(
% 1.50/0.60    r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.50/0.60    inference(subsumption_resolution,[],[f420,f117])).
% 1.50/0.60  fof(f117,plain,(
% 1.50/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.50/0.60    inference(subsumption_resolution,[],[f116,f83])).
% 1.50/0.60  fof(f83,plain,(
% 1.50/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.50/0.60    inference(equality_resolution,[],[f65])).
% 1.50/0.60  fof(f65,plain,(
% 1.50/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.50/0.60    inference(cnf_transformation,[],[f43])).
% 1.50/0.60  fof(f43,plain,(
% 1.50/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.50/0.60    inference(flattening,[],[f42])).
% 1.50/0.60  fof(f42,plain,(
% 1.50/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.50/0.60    inference(nnf_transformation,[],[f2])).
% 1.50/0.60  fof(f2,axiom,(
% 1.50/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.50/0.60  fof(f116,plain,(
% 1.50/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X0)) )),
% 1.50/0.60    inference(superposition,[],[f80,f79])).
% 1.50/0.60  fof(f79,plain,(
% 1.50/0.60    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.50/0.60    inference(definition_unfolding,[],[f55,f77])).
% 1.50/0.60  fof(f77,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.50/0.60    inference(definition_unfolding,[],[f56,f76])).
% 1.50/0.60  fof(f76,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.50/0.60    inference(definition_unfolding,[],[f57,f75])).
% 1.50/0.60  fof(f75,plain,(
% 1.50/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.50/0.60    inference(definition_unfolding,[],[f69,f74])).
% 1.50/0.60  fof(f74,plain,(
% 1.50/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.50/0.60    inference(definition_unfolding,[],[f72,f73])).
% 1.50/0.60  fof(f73,plain,(
% 1.50/0.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f9])).
% 1.50/0.60  fof(f9,axiom,(
% 1.50/0.60    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.50/0.60  fof(f72,plain,(
% 1.50/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f8])).
% 1.50/0.60  fof(f8,axiom,(
% 1.50/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.50/0.60  fof(f69,plain,(
% 1.50/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f7])).
% 1.50/0.60  fof(f7,axiom,(
% 1.50/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.50/0.60  fof(f57,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f6])).
% 1.50/0.60  fof(f6,axiom,(
% 1.50/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.50/0.60  fof(f56,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.50/0.60    inference(cnf_transformation,[],[f10])).
% 1.50/0.60  fof(f10,axiom,(
% 1.50/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.50/0.60  fof(f55,plain,(
% 1.50/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.50/0.60    inference(cnf_transformation,[],[f24])).
% 1.50/0.60  fof(f24,plain,(
% 1.50/0.60    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.50/0.60    inference(rectify,[],[f1])).
% 1.50/0.60  fof(f1,axiom,(
% 1.50/0.60    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.50/0.60  fof(f80,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) | ~r1_tarski(X0,X1)) )),
% 1.50/0.60    inference(definition_unfolding,[],[f68,f78])).
% 1.50/0.60  fof(f78,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 1.50/0.60    inference(definition_unfolding,[],[f58,f77])).
% 1.50/0.60  fof(f58,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.50/0.60    inference(cnf_transformation,[],[f4])).
% 1.50/0.60  fof(f4,axiom,(
% 1.50/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.50/0.60  fof(f68,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f44])).
% 1.50/0.60  fof(f44,plain,(
% 1.50/0.60    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.50/0.60    inference(nnf_transformation,[],[f3])).
% 1.50/0.60  fof(f3,axiom,(
% 1.50/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.50/0.60  fof(f420,plain,(
% 1.50/0.60    k1_xboole_0 != k5_xboole_0(sK0,sK0) | r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.50/0.60    inference(superposition,[],[f148,f410])).
% 1.50/0.60  fof(f410,plain,(
% 1.50/0.60    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 1.50/0.60    inference(subsumption_resolution,[],[f409,f45])).
% 1.50/0.60  fof(f45,plain,(
% 1.50/0.60    v1_relat_1(sK1)),
% 1.50/0.60    inference(cnf_transformation,[],[f40])).
% 1.50/0.60  fof(f409,plain,(
% 1.50/0.60    sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)),
% 1.50/0.60    inference(resolution,[],[f284,f59])).
% 1.50/0.60  fof(f59,plain,(
% 1.50/0.60    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f31])).
% 1.50/0.60  fof(f31,plain,(
% 1.50/0.60    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.50/0.60    inference(ennf_transformation,[],[f13])).
% 1.50/0.60  fof(f13,axiom,(
% 1.50/0.60    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.50/0.60  fof(f284,plain,(
% 1.50/0.60    ~v1_relat_1(k7_relat_1(sK1,sK0)) | sK0 = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),
% 1.50/0.60    inference(forward_demodulation,[],[f283,f266])).
% 1.50/0.60  fof(f266,plain,(
% 1.50/0.60    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 1.50/0.60    inference(forward_demodulation,[],[f263,f49])).
% 1.50/0.60  fof(f49,plain,(
% 1.50/0.60    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.50/0.60    inference(cnf_transformation,[],[f19])).
% 1.50/0.60  fof(f19,axiom,(
% 1.50/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.50/0.60  fof(f263,plain,(
% 1.50/0.60    k1_relat_1(k7_relat_1(sK1,sK0)) = k1_relat_1(k6_relat_1(sK0))),
% 1.50/0.60    inference(superposition,[],[f205,f257])).
% 1.50/0.60  fof(f257,plain,(
% 1.50/0.60    k6_relat_1(sK0) = k7_relat_1(k6_relat_1(sK0),k1_relat_1(sK1))),
% 1.50/0.60    inference(resolution,[],[f156,f46])).
% 1.50/0.60  fof(f46,plain,(
% 1.50/0.60    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.50/0.60    inference(cnf_transformation,[],[f40])).
% 1.50/0.60  fof(f156,plain,(
% 1.50/0.60    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 1.50/0.60    inference(forward_demodulation,[],[f154,f49])).
% 1.50/0.60  fof(f154,plain,(
% 1.50/0.60    ( ! [X2,X1] : (k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) | ~r1_tarski(k1_relat_1(k6_relat_1(X1)),X2)) )),
% 1.50/0.60    inference(resolution,[],[f100,f48])).
% 1.50/0.60  fof(f48,plain,(
% 1.50/0.60    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.50/0.60    inference(cnf_transformation,[],[f12])).
% 1.50/0.60  fof(f12,axiom,(
% 1.50/0.60    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.50/0.60  fof(f100,plain,(
% 1.50/0.60    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 | ~r1_tarski(k1_relat_1(X0),X1)) )),
% 1.50/0.60    inference(duplicate_literal_removal,[],[f99])).
% 1.50/0.60  fof(f99,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k7_relat_1(X0,X1) = X0 | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 1.50/0.60    inference(resolution,[],[f63,f62])).
% 1.50/0.60  fof(f62,plain,(
% 1.50/0.60    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f41])).
% 1.50/0.60  fof(f41,plain,(
% 1.50/0.60    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.50/0.60    inference(nnf_transformation,[],[f33])).
% 1.50/0.60  fof(f33,plain,(
% 1.50/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.50/0.60    inference(ennf_transformation,[],[f11])).
% 1.50/0.60  fof(f11,axiom,(
% 1.50/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.50/0.60  fof(f63,plain,(
% 1.50/0.60    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f35])).
% 1.50/0.60  fof(f35,plain,(
% 1.50/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.50/0.60    inference(flattening,[],[f34])).
% 1.50/0.60  fof(f34,plain,(
% 1.50/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.50/0.60    inference(ennf_transformation,[],[f18])).
% 1.50/0.60  fof(f18,axiom,(
% 1.50/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.50/0.60  fof(f205,plain,(
% 1.50/0.60    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)))) )),
% 1.50/0.60    inference(subsumption_resolution,[],[f198,f144])).
% 1.50/0.60  fof(f144,plain,(
% 1.50/0.60    ( ! [X2] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X2),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X2)))) )),
% 1.50/0.60    inference(subsumption_resolution,[],[f141,f48])).
% 1.50/0.60  fof(f141,plain,(
% 1.50/0.60    ( ! [X2] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X2),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X2))) | ~v1_relat_1(k6_relat_1(X2))) )),
% 1.50/0.60    inference(superposition,[],[f60,f131])).
% 1.50/0.60  fof(f131,plain,(
% 1.50/0.60    ( ! [X0] : (k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 1.50/0.60    inference(forward_demodulation,[],[f129,f49])).
% 1.50/0.60  fof(f129,plain,(
% 1.50/0.60    ( ! [X0] : (k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(sK1,k1_relat_1(k6_relat_1(X0)))))) )),
% 1.50/0.60    inference(resolution,[],[f124,f48])).
% 1.50/0.60  fof(f124,plain,(
% 1.50/0.60    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(sK1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(X0))))) )),
% 1.50/0.60    inference(resolution,[],[f53,f45])).
% 1.50/0.60  fof(f53,plain,(
% 1.50/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f29])).
% 1.50/0.60  fof(f29,plain,(
% 1.50/0.60    ! [X0] : (! [X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.50/0.60    inference(ennf_transformation,[],[f17])).
% 1.50/0.60  fof(f17,axiom,(
% 1.50/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).
% 1.50/0.60  fof(f60,plain,(
% 1.50/0.60    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f32])).
% 1.50/0.60  fof(f32,plain,(
% 1.50/0.60    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.50/0.60    inference(ennf_transformation,[],[f20])).
% 1.50/0.60  fof(f20,axiom,(
% 1.50/0.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 1.50/0.60  fof(f198,plain,(
% 1.50/0.60    ( ! [X0] : (~r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))),k1_relat_1(k7_relat_1(sK1,X0))) | k1_relat_1(k7_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)))) )),
% 1.50/0.60    inference(superposition,[],[f175,f181])).
% 1.50/0.60  fof(f181,plain,(
% 1.50/0.60    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1))))) )),
% 1.50/0.60    inference(resolution,[],[f127,f45])).
% 1.50/0.60  fof(f127,plain,(
% 1.50/0.60    ( ! [X2,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,k1_relat_1(k7_relat_1(k6_relat_1(X2),k1_relat_1(X1)))) = k7_relat_1(X1,X2)) )),
% 1.50/0.60    inference(forward_demodulation,[],[f125,f49])).
% 1.50/0.60  fof(f125,plain,(
% 1.50/0.60    ( ! [X2,X1] : (k7_relat_1(X1,k1_relat_1(k6_relat_1(X2))) = k7_relat_1(X1,k1_relat_1(k7_relat_1(k6_relat_1(X2),k1_relat_1(X1)))) | ~v1_relat_1(X1)) )),
% 1.50/0.60    inference(resolution,[],[f53,f48])).
% 1.50/0.60  fof(f175,plain,(
% 1.50/0.60    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k7_relat_1(sK1,X0))) | k1_relat_1(k7_relat_1(sK1,X0)) = X0) )),
% 1.50/0.60    inference(resolution,[],[f95,f45])).
% 1.50/0.60  fof(f95,plain,(
% 1.50/0.60    ( ! [X2,X1] : (~v1_relat_1(X2) | ~r1_tarski(X1,k1_relat_1(k7_relat_1(X2,X1))) | k1_relat_1(k7_relat_1(X2,X1)) = X1) )),
% 1.50/0.60    inference(resolution,[],[f66,f60])).
% 1.50/0.60  fof(f66,plain,(
% 1.50/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f43])).
% 1.50/0.60  fof(f283,plain,(
% 1.50/0.60    k1_relat_1(k7_relat_1(sK1,sK0)) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) | ~v1_relat_1(k7_relat_1(sK1,sK0))),
% 1.50/0.60    inference(superposition,[],[f51,f277])).
% 1.50/0.60  fof(f277,plain,(
% 1.50/0.60    k9_relat_1(sK1,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))),
% 1.50/0.60    inference(superposition,[],[f171,f266])).
% 1.50/0.60  fof(f171,plain,(
% 1.50/0.60    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 1.50/0.60    inference(resolution,[],[f110,f45])).
% 1.50/0.60  fof(f110,plain,(
% 1.50/0.60    ( ! [X4,X3] : (~v1_relat_1(X3) | k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4)))) )),
% 1.50/0.60    inference(subsumption_resolution,[],[f109,f59])).
% 1.50/0.60  fof(f109,plain,(
% 1.50/0.60    ( ! [X4,X3] : (k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4))) | ~v1_relat_1(X3) | ~v1_relat_1(k7_relat_1(X3,X4))) )),
% 1.50/0.60    inference(subsumption_resolution,[],[f107,f60])).
% 1.50/0.60  fof(f107,plain,(
% 1.50/0.60    ( ! [X4,X3] : (k2_relat_1(k7_relat_1(X3,X4)) = k9_relat_1(X3,k1_relat_1(k7_relat_1(X3,X4))) | ~r1_tarski(k1_relat_1(k7_relat_1(X3,X4)),X4) | ~v1_relat_1(X3) | ~v1_relat_1(k7_relat_1(X3,X4))) )),
% 1.50/0.60    inference(superposition,[],[f54,f52])).
% 1.50/0.60  fof(f52,plain,(
% 1.50/0.60    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f28])).
% 1.50/0.60  fof(f28,plain,(
% 1.50/0.60    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.60    inference(ennf_transformation,[],[f14])).
% 1.50/0.60  fof(f14,axiom,(
% 1.50/0.60    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 1.50/0.60  fof(f54,plain,(
% 1.50/0.60    ( ! [X2,X0,X1] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f30])).
% 1.50/0.60  fof(f30,plain,(
% 1.50/0.60    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 1.50/0.60    inference(ennf_transformation,[],[f15])).
% 1.50/0.60  fof(f15,axiom,(
% 1.50/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 1.50/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).
% 1.50/0.60  fof(f51,plain,(
% 1.50/0.60    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f27])).
% 1.50/0.60  fof(f27,plain,(
% 1.50/0.60    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.50/0.60    inference(ennf_transformation,[],[f16])).
% 1.50/0.61  fof(f16,axiom,(
% 1.50/0.61    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 1.50/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.50/0.61  fof(f148,plain,(
% 1.50/0.61    ( ! [X2,X1] : (k1_xboole_0 != k5_xboole_0(X1,k10_relat_1(k7_relat_1(sK1,X1),X2)) | r1_tarski(X1,k10_relat_1(sK1,X2))) )),
% 1.50/0.61    inference(superposition,[],[f81,f132])).
% 1.50/0.61  fof(f132,plain,(
% 1.50/0.61    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK1,X0),X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k10_relat_1(sK1,X1)))) )),
% 1.50/0.61    inference(resolution,[],[f82,f45])).
% 1.50/0.61  fof(f82,plain,(
% 1.50/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k10_relat_1(X2,X1)))) )),
% 1.50/0.61    inference(definition_unfolding,[],[f70,f77])).
% 1.50/0.61  fof(f70,plain,(
% 1.50/0.61    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.50/0.61    inference(cnf_transformation,[],[f36])).
% 1.50/0.61  fof(f36,plain,(
% 1.50/0.61    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.50/0.61    inference(ennf_transformation,[],[f21])).
% 1.50/0.61  fof(f21,axiom,(
% 1.50/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.50/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 1.50/0.61  fof(f81,plain,(
% 1.50/0.61    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) | r1_tarski(X0,X1)) )),
% 1.50/0.61    inference(definition_unfolding,[],[f67,f78])).
% 1.50/0.61  fof(f67,plain,(
% 1.50/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.50/0.61    inference(cnf_transformation,[],[f44])).
% 1.50/0.61  % SZS output end Proof for theBenchmark
% 1.50/0.61  % (22210)------------------------------
% 1.50/0.61  % (22210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.61  % (22210)Termination reason: Refutation
% 1.50/0.61  
% 1.50/0.61  % (22210)Memory used [KB]: 6652
% 1.50/0.61  % (22210)Time elapsed: 0.173 s
% 1.50/0.62  % (22210)------------------------------
% 1.50/0.62  % (22210)------------------------------
% 1.50/0.62  % (22187)Success in time 0.259 s
%------------------------------------------------------------------------------
