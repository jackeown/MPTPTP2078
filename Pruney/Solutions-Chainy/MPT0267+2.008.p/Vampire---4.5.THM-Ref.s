%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:35 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   97 (2629 expanded)
%              Number of leaves         :   15 ( 816 expanded)
%              Depth                    :   35
%              Number of atoms          :  190 (3834 expanded)
%              Number of equality atoms :   69 (2160 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f383,plain,(
    $false ),
    inference(subsumption_resolution,[],[f382,f98])).

fof(f98,plain,(
    ! [X2] : r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f36,f72])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f52,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f382,plain,(
    ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f362,f294])).

fof(f294,plain,(
    r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(backward_demodulation,[],[f179,f289])).

fof(f289,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f288,f96])).

fof(f96,plain,(
    ! [X2,X0] :
      ( X0 = X2
      | ~ r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f37,f72])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f288,plain,
    ( sK0 = sK2
    | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(subsumption_resolution,[],[f267,f179])).

fof(f267,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(resolution,[],[f265,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f265,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))
    | sK0 = sK2 ),
    inference(subsumption_resolution,[],[f245,f213])).

fof(f213,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f193,f180])).

fof(f180,plain,
    ( ~ r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f158,f179])).

fof(f158,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | ~ r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(resolution,[],[f156,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f156,plain,
    ( r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))
    | r2_hidden(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f134,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f134,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))
    | r2_hidden(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f111,f48])).

fof(f111,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))))
    | r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f74,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f74,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) ),
    inference(definition_unfolding,[],[f26,f71,f72])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f34,f70])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f35,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f68])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f26,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <~> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      <=> ( X0 != X2
          & r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f193,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(resolution,[],[f179,f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f45,f69])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f245,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f243,f49])).

fof(f243,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))
    | sK0 = sK2 ),
    inference(subsumption_resolution,[],[f242,f213])).

fof(f242,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK2
    | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) ),
    inference(duplicate_literal_removal,[],[f222])).

fof(f222,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK2
    | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f112,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f112,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))))
    | ~ r2_hidden(sK0,sK1)
    | sK0 = sK2 ),
    inference(forward_demodulation,[],[f75,f41])).

fof(f75,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK2
    | ~ r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) ),
    inference(definition_unfolding,[],[f25,f71,f72])).

fof(f25,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK2
    | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f179,plain,(
    r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(subsumption_resolution,[],[f178,f100])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f178,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(subsumption_resolution,[],[f157,f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f47,f69])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f157,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(resolution,[],[f156,f48])).

fof(f362,plain,
    ( ~ r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f360,f49])).

fof(f360,plain,(
    r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) ),
    inference(subsumption_resolution,[],[f340,f213])).

fof(f340,plain,
    ( r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f338,f51])).

fof(f338,plain,(
    ~ r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) ),
    inference(subsumption_resolution,[],[f318,f213])).

fof(f318,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f296,f49])).

fof(f296,plain,(
    r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))) ),
    inference(trivial_inequality_removal,[],[f290])).

fof(f290,plain,
    ( sK0 != sK0
    | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))) ),
    inference(backward_demodulation,[],[f110,f289])).

fof(f110,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))) ),
    inference(inner_rewriting,[],[f109])).

fof(f109,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))))
    | sK0 != sK2 ),
    inference(forward_demodulation,[],[f73,f41])).

fof(f73,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) ),
    inference(definition_unfolding,[],[f27,f71,f72])).

fof(f27,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:29:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (5732)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (5749)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (5754)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (5746)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (5729)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (5727)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.24/0.53  % (5741)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.24/0.53  % (5741)Refutation not found, incomplete strategy% (5741)------------------------------
% 1.24/0.53  % (5741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (5741)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (5741)Memory used [KB]: 1663
% 1.24/0.53  % (5741)Time elapsed: 0.072 s
% 1.24/0.53  % (5741)------------------------------
% 1.24/0.53  % (5741)------------------------------
% 1.24/0.53  % (5733)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.24/0.54  % (5728)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.24/0.54  % (5736)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.24/0.54  % (5731)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.24/0.54  % (5728)Refutation not found, incomplete strategy% (5728)------------------------------
% 1.24/0.54  % (5728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (5728)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (5728)Memory used [KB]: 1663
% 1.24/0.54  % (5728)Time elapsed: 0.125 s
% 1.24/0.54  % (5728)------------------------------
% 1.24/0.54  % (5728)------------------------------
% 1.24/0.54  % (5735)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.24/0.54  % (5752)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.24/0.54  % (5753)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.41/0.54  % (5747)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.41/0.55  % (5730)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.41/0.55  % (5748)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.41/0.55  % (5740)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.41/0.55  % (5755)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.41/0.55  % (5751)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.41/0.55  % (5756)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.41/0.55  % (5750)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.41/0.55  % (5756)Refutation not found, incomplete strategy% (5756)------------------------------
% 1.41/0.55  % (5756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (5756)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (5756)Memory used [KB]: 1663
% 1.41/0.55  % (5756)Time elapsed: 0.138 s
% 1.41/0.55  % (5756)------------------------------
% 1.41/0.55  % (5756)------------------------------
% 1.41/0.55  % (5745)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.41/0.55  % (5744)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.41/0.55  % (5743)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.41/0.55  % (5734)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.41/0.55  % (5739)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.41/0.56  % (5743)Refutation not found, incomplete strategy% (5743)------------------------------
% 1.41/0.56  % (5743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (5743)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (5743)Memory used [KB]: 10618
% 1.41/0.56  % (5743)Time elapsed: 0.131 s
% 1.41/0.56  % (5743)------------------------------
% 1.41/0.56  % (5743)------------------------------
% 1.41/0.56  % (5744)Refutation found. Thanks to Tanya!
% 1.41/0.56  % SZS status Theorem for theBenchmark
% 1.41/0.56  % SZS output start Proof for theBenchmark
% 1.41/0.56  fof(f383,plain,(
% 1.41/0.56    $false),
% 1.41/0.56    inference(subsumption_resolution,[],[f382,f98])).
% 1.41/0.56  fof(f98,plain,(
% 1.41/0.56    ( ! [X2] : (r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) )),
% 1.41/0.56    inference(equality_resolution,[],[f97])).
% 1.41/0.56  fof(f97,plain,(
% 1.41/0.56    ( ! [X2,X1] : (r2_hidden(X2,X1) | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1) )),
% 1.41/0.56    inference(equality_resolution,[],[f81])).
% 1.41/0.56  fof(f81,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.41/0.56    inference(definition_unfolding,[],[f36,f72])).
% 1.41/0.56  fof(f72,plain,(
% 1.41/0.56    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.41/0.56    inference(definition_unfolding,[],[f30,f68])).
% 1.41/0.56  fof(f68,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.41/0.56    inference(definition_unfolding,[],[f33,f67])).
% 1.41/0.56  fof(f67,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.41/0.56    inference(definition_unfolding,[],[f40,f66])).
% 1.41/0.56  fof(f66,plain,(
% 1.41/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.41/0.56    inference(definition_unfolding,[],[f52,f65])).
% 1.41/0.56  fof(f65,plain,(
% 1.41/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.41/0.56    inference(definition_unfolding,[],[f61,f64])).
% 1.41/0.56  fof(f64,plain,(
% 1.41/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.41/0.56    inference(definition_unfolding,[],[f62,f63])).
% 1.41/0.56  fof(f63,plain,(
% 1.41/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f16])).
% 1.41/0.56  fof(f16,axiom,(
% 1.41/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.41/0.56  fof(f62,plain,(
% 1.41/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f15])).
% 1.41/0.56  fof(f15,axiom,(
% 1.41/0.56    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.41/0.56  fof(f61,plain,(
% 1.41/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f14])).
% 1.41/0.56  fof(f14,axiom,(
% 1.41/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.41/0.56  fof(f52,plain,(
% 1.41/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f13])).
% 1.41/0.56  fof(f13,axiom,(
% 1.41/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.41/0.56  fof(f40,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f12])).
% 1.41/0.56  fof(f12,axiom,(
% 1.41/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.41/0.56  fof(f33,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f11])).
% 1.41/0.56  fof(f11,axiom,(
% 1.41/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.41/0.56  fof(f30,plain,(
% 1.41/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f10])).
% 1.41/0.56  fof(f10,axiom,(
% 1.41/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.41/0.56  fof(f36,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.41/0.56    inference(cnf_transformation,[],[f9])).
% 1.41/0.56  fof(f9,axiom,(
% 1.41/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.41/0.56  fof(f382,plain,(
% 1.41/0.56    ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.41/0.56    inference(subsumption_resolution,[],[f362,f294])).
% 1.41/0.56  fof(f294,plain,(
% 1.41/0.56    r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.41/0.56    inference(backward_demodulation,[],[f179,f289])).
% 1.41/0.56  fof(f289,plain,(
% 1.41/0.56    sK0 = sK2),
% 1.41/0.56    inference(subsumption_resolution,[],[f288,f96])).
% 1.41/0.56  fof(f96,plain,(
% 1.41/0.56    ( ! [X2,X0] : (X0 = X2 | ~r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 1.41/0.56    inference(equality_resolution,[],[f80])).
% 1.41/0.56  fof(f80,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.41/0.56    inference(definition_unfolding,[],[f37,f72])).
% 1.41/0.56  fof(f37,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.41/0.56    inference(cnf_transformation,[],[f9])).
% 1.41/0.56  fof(f288,plain,(
% 1.41/0.56    sK0 = sK2 | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.41/0.56    inference(subsumption_resolution,[],[f267,f179])).
% 1.41/0.56  fof(f267,plain,(
% 1.41/0.56    sK0 = sK2 | ~r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.41/0.56    inference(resolution,[],[f265,f50])).
% 1.41/0.56  fof(f50,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | r2_hidden(X0,X1) | r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f23])).
% 1.41/0.56  fof(f23,plain,(
% 1.41/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.41/0.56    inference(ennf_transformation,[],[f3])).
% 1.41/0.56  fof(f3,axiom,(
% 1.41/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.41/0.56  fof(f265,plain,(
% 1.41/0.56    ~r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) | sK0 = sK2),
% 1.41/0.56    inference(subsumption_resolution,[],[f245,f213])).
% 1.41/0.56  fof(f213,plain,(
% 1.41/0.56    r2_hidden(sK0,sK1)),
% 1.41/0.56    inference(subsumption_resolution,[],[f193,f180])).
% 1.41/0.56  fof(f180,plain,(
% 1.41/0.56    ~r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | r2_hidden(sK0,sK1)),
% 1.41/0.56    inference(subsumption_resolution,[],[f158,f179])).
% 1.41/0.56  fof(f158,plain,(
% 1.41/0.56    r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | ~r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.41/0.56    inference(resolution,[],[f156,f49])).
% 1.41/0.56  fof(f49,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f23])).
% 1.41/0.56  fof(f156,plain,(
% 1.41/0.56    r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) | r2_hidden(sK0,sK1)),
% 1.41/0.56    inference(duplicate_literal_removal,[],[f135])).
% 1.41/0.56  fof(f135,plain,(
% 1.41/0.56    r2_hidden(sK0,sK1) | r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) | r2_hidden(sK0,sK1)),
% 1.41/0.56    inference(resolution,[],[f134,f48])).
% 1.41/0.56  fof(f48,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f23])).
% 1.41/0.56  fof(f134,plain,(
% 1.41/0.56    r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) | r2_hidden(sK0,sK1)),
% 1.41/0.56    inference(duplicate_literal_removal,[],[f113])).
% 1.41/0.56  fof(f113,plain,(
% 1.41/0.56    r2_hidden(sK0,sK1) | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) | r2_hidden(sK0,sK1)),
% 1.41/0.56    inference(resolution,[],[f111,f48])).
% 1.41/0.56  fof(f111,plain,(
% 1.41/0.56    r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) | r2_hidden(sK0,sK1)),
% 1.41/0.56    inference(forward_demodulation,[],[f74,f41])).
% 1.41/0.56  fof(f41,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f5])).
% 1.41/0.56  fof(f5,axiom,(
% 1.41/0.56    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.41/0.56  fof(f74,plain,(
% 1.41/0.56    r2_hidden(sK0,sK1) | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))),
% 1.41/0.56    inference(definition_unfolding,[],[f26,f71,f72])).
% 1.41/0.56  fof(f71,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 1.41/0.56    inference(definition_unfolding,[],[f34,f70])).
% 1.41/0.56  fof(f70,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.41/0.56    inference(definition_unfolding,[],[f35,f69])).
% 1.41/0.56  fof(f69,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.41/0.56    inference(definition_unfolding,[],[f32,f68])).
% 1.41/0.56  fof(f32,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f17])).
% 1.41/0.56  fof(f17,axiom,(
% 1.41/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.41/0.56  fof(f35,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f7])).
% 1.41/0.56  fof(f7,axiom,(
% 1.41/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.41/0.56  fof(f34,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f4])).
% 1.41/0.56  fof(f4,axiom,(
% 1.41/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.41/0.56  fof(f26,plain,(
% 1.41/0.56    r2_hidden(sK0,sK1) | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 1.41/0.56    inference(cnf_transformation,[],[f22])).
% 1.41/0.56  fof(f22,plain,(
% 1.41/0.56    ? [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <~> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.41/0.56    inference(ennf_transformation,[],[f20])).
% 1.41/0.56  fof(f20,negated_conjecture,(
% 1.41/0.56    ~! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.41/0.56    inference(negated_conjecture,[],[f19])).
% 1.41/0.56  fof(f19,conjecture,(
% 1.41/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.41/0.56  fof(f193,plain,(
% 1.41/0.56    r2_hidden(sK0,sK1) | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.41/0.56    inference(resolution,[],[f179,f101])).
% 1.41/0.56  fof(f101,plain,(
% 1.41/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.41/0.56    inference(equality_resolution,[],[f84])).
% 1.41/0.56  fof(f84,plain,(
% 1.41/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.41/0.56    inference(definition_unfolding,[],[f45,f69])).
% 1.41/0.56  fof(f45,plain,(
% 1.41/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.41/0.56    inference(cnf_transformation,[],[f1])).
% 1.41/0.56  fof(f1,axiom,(
% 1.41/0.56    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.41/0.56  fof(f245,plain,(
% 1.41/0.56    sK0 = sK2 | ~r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) | ~r2_hidden(sK0,sK1)),
% 1.41/0.56    inference(resolution,[],[f243,f49])).
% 1.41/0.56  fof(f243,plain,(
% 1.41/0.56    r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) | sK0 = sK2),
% 1.41/0.56    inference(subsumption_resolution,[],[f242,f213])).
% 1.41/0.56  fof(f242,plain,(
% 1.41/0.56    ~r2_hidden(sK0,sK1) | sK0 = sK2 | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))),
% 1.41/0.56    inference(duplicate_literal_removal,[],[f222])).
% 1.41/0.56  fof(f222,plain,(
% 1.41/0.56    ~r2_hidden(sK0,sK1) | sK0 = sK2 | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) | ~r2_hidden(sK0,sK1)),
% 1.41/0.56    inference(resolution,[],[f112,f51])).
% 1.41/0.56  fof(f51,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f23])).
% 1.41/0.56  fof(f112,plain,(
% 1.41/0.56    ~r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) | ~r2_hidden(sK0,sK1) | sK0 = sK2),
% 1.41/0.56    inference(forward_demodulation,[],[f75,f41])).
% 1.41/0.56  fof(f75,plain,(
% 1.41/0.56    ~r2_hidden(sK0,sK1) | sK0 = sK2 | ~r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))),
% 1.41/0.56    inference(definition_unfolding,[],[f25,f71,f72])).
% 1.41/0.56  fof(f25,plain,(
% 1.41/0.56    ~r2_hidden(sK0,sK1) | sK0 = sK2 | ~r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 1.41/0.56    inference(cnf_transformation,[],[f22])).
% 1.41/0.56  fof(f179,plain,(
% 1.41/0.56    r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.41/0.56    inference(subsumption_resolution,[],[f178,f100])).
% 1.41/0.56  fof(f100,plain,(
% 1.41/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.41/0.56    inference(equality_resolution,[],[f83])).
% 1.41/0.56  fof(f83,plain,(
% 1.41/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.41/0.56    inference(definition_unfolding,[],[f46,f69])).
% 1.41/0.56  fof(f46,plain,(
% 1.41/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.41/0.56    inference(cnf_transformation,[],[f1])).
% 1.41/0.56  fof(f178,plain,(
% 1.41/0.56    r2_hidden(sK0,sK1) | r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.41/0.56    inference(subsumption_resolution,[],[f157,f99])).
% 1.41/0.56  fof(f99,plain,(
% 1.41/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.41/0.56    inference(equality_resolution,[],[f82])).
% 1.41/0.56  fof(f82,plain,(
% 1.41/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.41/0.56    inference(definition_unfolding,[],[f47,f69])).
% 1.41/0.56  fof(f47,plain,(
% 1.41/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.41/0.56    inference(cnf_transformation,[],[f1])).
% 1.41/0.56  fof(f157,plain,(
% 1.41/0.56    r2_hidden(sK0,sK1) | r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.41/0.56    inference(resolution,[],[f156,f48])).
% 1.41/0.56  fof(f362,plain,(
% 1.41/0.56    ~r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.41/0.56    inference(resolution,[],[f360,f49])).
% 1.41/0.56  fof(f360,plain,(
% 1.41/0.56    r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))),
% 1.41/0.56    inference(subsumption_resolution,[],[f340,f213])).
% 1.41/0.56  fof(f340,plain,(
% 1.41/0.56    r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) | ~r2_hidden(sK0,sK1)),
% 1.41/0.56    inference(resolution,[],[f338,f51])).
% 1.41/0.56  fof(f338,plain,(
% 1.41/0.56    ~r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))),
% 1.41/0.56    inference(subsumption_resolution,[],[f318,f213])).
% 1.41/0.56  fof(f318,plain,(
% 1.41/0.56    ~r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) | ~r2_hidden(sK0,sK1)),
% 1.41/0.56    inference(resolution,[],[f296,f49])).
% 1.41/0.56  fof(f296,plain,(
% 1.41/0.56    r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))))),
% 1.41/0.56    inference(trivial_inequality_removal,[],[f290])).
% 1.41/0.56  fof(f290,plain,(
% 1.41/0.56    sK0 != sK0 | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))))),
% 1.41/0.56    inference(backward_demodulation,[],[f110,f289])).
% 1.41/0.56  fof(f110,plain,(
% 1.41/0.56    sK0 != sK2 | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))))),
% 1.41/0.56    inference(inner_rewriting,[],[f109])).
% 1.41/0.56  fof(f109,plain,(
% 1.41/0.56    r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) | sK0 != sK2),
% 1.41/0.56    inference(forward_demodulation,[],[f73,f41])).
% 1.41/0.56  fof(f73,plain,(
% 1.41/0.56    sK0 != sK2 | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))),
% 1.41/0.56    inference(definition_unfolding,[],[f27,f71,f72])).
% 1.41/0.56  fof(f27,plain,(
% 1.41/0.56    sK0 != sK2 | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 1.41/0.56    inference(cnf_transformation,[],[f22])).
% 1.41/0.56  % SZS output end Proof for theBenchmark
% 1.41/0.56  % (5744)------------------------------
% 1.41/0.56  % (5744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (5744)Termination reason: Refutation
% 1.41/0.56  
% 1.41/0.56  % (5744)Memory used [KB]: 1791
% 1.41/0.56  % (5744)Time elapsed: 0.141 s
% 1.41/0.56  % (5744)------------------------------
% 1.41/0.56  % (5744)------------------------------
% 1.41/0.56  % (5738)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.41/0.56  % (5737)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.41/0.56  % (5742)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.41/0.58  % (5724)Success in time 0.216 s
%------------------------------------------------------------------------------
