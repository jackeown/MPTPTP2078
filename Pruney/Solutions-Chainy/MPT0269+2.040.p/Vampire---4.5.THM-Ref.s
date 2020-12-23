%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:52 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 355 expanded)
%              Number of leaves         :   22 ( 115 expanded)
%              Depth                    :   23
%              Number of atoms          :  150 ( 450 expanded)
%              Number of equality atoms :   82 ( 379 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1132,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f40,f999,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f999,plain,(
    r1_xboole_0(sK0,sK0) ),
    inference(resolution,[],[f993,f992])).

fof(f992,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f989,f74])).

fof(f74,plain,(
    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f41,f73])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( sK0 != k1_tarski(sK1)
    & k1_xboole_0 != sK0
    & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f37])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( sK0 != k1_tarski(sK1)
      & k1_xboole_0 != sK0
      & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f989,plain,
    ( sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f691,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f80,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f691,plain,(
    ~ r2_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) ),
    inference(superposition,[],[f109,f273])).

fof(f273,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f272,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f272,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f258,f106])).

fof(f106,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f84,f100])).

fof(f100,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f93,f44])).

fof(f93,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f84,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f84,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f59,f42])).

fof(f59,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f258,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0))) ),
    inference(superposition,[],[f142,f42])).

fof(f142,plain,(
    ! [X0] : k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),X0)))) = X0 ),
    inference(forward_demodulation,[],[f141,f100])).

fof(f141,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),X0)))) ),
    inference(forward_demodulation,[],[f140,f59])).

fof(f140,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),X0))) ),
    inference(forward_demodulation,[],[f138,f59])).

fof(f138,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),X0)) ),
    inference(superposition,[],[f59,f122])).

fof(f122,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))) ),
    inference(forward_demodulation,[],[f75,f59])).

fof(f75,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))) ),
    inference(definition_unfolding,[],[f39,f72,f73])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f52,f71])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f53,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f69])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f39,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f109,plain,(
    ! [X2,X3] : ~ r2_xboole_0(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),X2) ),
    inference(resolution,[],[f78,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f49,f70])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f993,plain,(
    ! [X0] :
      ( r2_hidden(sK1,X0)
      | r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f692,f112])).

fof(f112,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X3,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | r1_xboole_0(X3,X2)
      | r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f79,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f73])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f692,plain,(
    r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f78,f273])).

fof(f40,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:05:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.51  % (15792)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (15792)Refutation not found, incomplete strategy% (15792)------------------------------
% 0.22/0.51  % (15792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15817)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (15800)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (15792)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (15792)Memory used [KB]: 1791
% 0.22/0.52  % (15792)Time elapsed: 0.094 s
% 0.22/0.52  % (15792)------------------------------
% 0.22/0.52  % (15792)------------------------------
% 0.22/0.52  % (15796)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (15797)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (15800)Refutation not found, incomplete strategy% (15800)------------------------------
% 0.22/0.52  % (15800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15800)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (15800)Memory used [KB]: 10746
% 0.22/0.52  % (15800)Time elapsed: 0.107 s
% 0.22/0.52  % (15800)------------------------------
% 0.22/0.52  % (15800)------------------------------
% 0.22/0.53  % (15795)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (15802)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (15802)Refutation not found, incomplete strategy% (15802)------------------------------
% 0.22/0.53  % (15802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15802)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15802)Memory used [KB]: 10618
% 0.22/0.53  % (15802)Time elapsed: 0.116 s
% 0.22/0.53  % (15802)------------------------------
% 0.22/0.53  % (15802)------------------------------
% 0.22/0.54  % (15798)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (15794)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (15818)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (15794)Refutation not found, incomplete strategy% (15794)------------------------------
% 0.22/0.54  % (15794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (15794)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (15794)Memory used [KB]: 10746
% 0.22/0.54  % (15794)Time elapsed: 0.126 s
% 0.22/0.54  % (15794)------------------------------
% 0.22/0.54  % (15794)------------------------------
% 0.22/0.55  % (15793)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (15820)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (15815)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (15815)Refutation not found, incomplete strategy% (15815)------------------------------
% 0.22/0.55  % (15815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (15815)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (15815)Memory used [KB]: 10746
% 0.22/0.55  % (15815)Time elapsed: 0.135 s
% 0.22/0.55  % (15815)------------------------------
% 0.22/0.55  % (15815)------------------------------
% 0.22/0.55  % (15821)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (15822)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (15810)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (15809)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (15801)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (15816)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (15810)Refutation not found, incomplete strategy% (15810)------------------------------
% 0.22/0.56  % (15810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (15810)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (15810)Memory used [KB]: 10618
% 0.22/0.56  % (15810)Time elapsed: 0.149 s
% 0.22/0.56  % (15810)------------------------------
% 0.22/0.56  % (15810)------------------------------
% 0.22/0.56  % (15806)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (15801)Refutation not found, incomplete strategy% (15801)------------------------------
% 0.22/0.56  % (15801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (15801)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (15801)Memory used [KB]: 10746
% 0.22/0.56  % (15801)Time elapsed: 0.149 s
% 0.22/0.56  % (15801)------------------------------
% 0.22/0.56  % (15801)------------------------------
% 0.22/0.56  % (15804)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (15814)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (15812)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (15814)Refutation not found, incomplete strategy% (15814)------------------------------
% 0.22/0.56  % (15814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (15814)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (15814)Memory used [KB]: 1791
% 0.22/0.56  % (15814)Time elapsed: 0.149 s
% 0.22/0.56  % (15814)------------------------------
% 0.22/0.56  % (15814)------------------------------
% 0.22/0.56  % (15805)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.54/0.56  % (15813)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.54/0.56  % (15819)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.54/0.57  % (15813)Refutation not found, incomplete strategy% (15813)------------------------------
% 1.54/0.57  % (15813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (15813)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (15813)Memory used [KB]: 10746
% 1.54/0.57  % (15813)Time elapsed: 0.151 s
% 1.54/0.57  % (15813)------------------------------
% 1.54/0.57  % (15813)------------------------------
% 1.54/0.57  % (15803)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.54/0.57  % (15803)Refutation not found, incomplete strategy% (15803)------------------------------
% 1.54/0.57  % (15803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (15803)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (15803)Memory used [KB]: 10618
% 1.54/0.57  % (15803)Time elapsed: 0.159 s
% 1.54/0.57  % (15803)------------------------------
% 1.54/0.57  % (15803)------------------------------
% 1.54/0.57  % (15807)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.54/0.57  % (15811)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.54/0.58  % (15799)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.54/0.58  % (15816)Refutation not found, incomplete strategy% (15816)------------------------------
% 1.54/0.58  % (15816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.59  % (15816)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.59  
% 1.69/0.59  % (15816)Memory used [KB]: 1663
% 1.69/0.59  % (15816)Time elapsed: 0.101 s
% 1.69/0.59  % (15816)------------------------------
% 1.69/0.59  % (15816)------------------------------
% 1.69/0.62  % (15822)Refutation found. Thanks to Tanya!
% 1.69/0.62  % SZS status Theorem for theBenchmark
% 1.69/0.62  % SZS output start Proof for theBenchmark
% 1.69/0.62  fof(f1132,plain,(
% 1.69/0.62    $false),
% 1.69/0.62    inference(unit_resulting_resolution,[],[f40,f999,f47])).
% 1.69/0.62  fof(f47,plain,(
% 1.69/0.62    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.69/0.62    inference(cnf_transformation,[],[f29])).
% 1.69/0.62  fof(f29,plain,(
% 1.69/0.62    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.69/0.62    inference(ennf_transformation,[],[f7])).
% 1.69/0.62  fof(f7,axiom,(
% 1.69/0.62    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.69/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.69/0.62  fof(f999,plain,(
% 1.69/0.62    r1_xboole_0(sK0,sK0)),
% 1.69/0.62    inference(resolution,[],[f993,f992])).
% 1.69/0.62  fof(f992,plain,(
% 1.69/0.62    ~r2_hidden(sK1,sK0)),
% 1.69/0.62    inference(subsumption_resolution,[],[f989,f74])).
% 1.69/0.62  fof(f74,plain,(
% 1.69/0.62    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 1.69/0.62    inference(definition_unfolding,[],[f41,f73])).
% 1.69/0.62  fof(f73,plain,(
% 1.69/0.62    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.69/0.62    inference(definition_unfolding,[],[f45,f69])).
% 1.69/0.62  fof(f69,plain,(
% 1.69/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.69/0.62    inference(definition_unfolding,[],[f51,f68])).
% 1.69/0.62  fof(f68,plain,(
% 1.69/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.69/0.62    inference(definition_unfolding,[],[f58,f67])).
% 2.05/0.65  fof(f67,plain,(
% 2.05/0.65    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.05/0.65    inference(definition_unfolding,[],[f61,f66])).
% 2.05/0.65  fof(f66,plain,(
% 2.05/0.65    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.05/0.65    inference(definition_unfolding,[],[f62,f65])).
% 2.05/0.65  fof(f65,plain,(
% 2.05/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.05/0.65    inference(definition_unfolding,[],[f63,f64])).
% 2.05/0.65  fof(f64,plain,(
% 2.05/0.65    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f18])).
% 2.05/0.65  fof(f18,axiom,(
% 2.05/0.65    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.05/0.65  fof(f63,plain,(
% 2.05/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f17])).
% 2.05/0.65  fof(f17,axiom,(
% 2.05/0.65    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.05/0.65  fof(f62,plain,(
% 2.05/0.65    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f16])).
% 2.05/0.65  fof(f16,axiom,(
% 2.05/0.65    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.05/0.65  fof(f61,plain,(
% 2.05/0.65    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f15])).
% 2.05/0.65  fof(f15,axiom,(
% 2.05/0.65    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.05/0.65  fof(f58,plain,(
% 2.05/0.65    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f14])).
% 2.05/0.65  fof(f14,axiom,(
% 2.05/0.65    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.05/0.65  fof(f51,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f13])).
% 2.05/0.65  fof(f13,axiom,(
% 2.05/0.65    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.05/0.65  fof(f45,plain,(
% 2.05/0.65    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f12])).
% 2.05/0.65  fof(f12,axiom,(
% 2.05/0.65    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.05/0.65  fof(f41,plain,(
% 2.05/0.65    sK0 != k1_tarski(sK1)),
% 2.05/0.65    inference(cnf_transformation,[],[f38])).
% 2.05/0.65  fof(f38,plain,(
% 2.05/0.65    sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 2.05/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f37])).
% 2.05/0.65  fof(f37,plain,(
% 2.05/0.65    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1))) => (sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 2.05/0.65    introduced(choice_axiom,[])).
% 2.05/0.65  fof(f28,plain,(
% 2.05/0.65    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 2.05/0.65    inference(ennf_transformation,[],[f24])).
% 2.05/0.65  fof(f24,negated_conjecture,(
% 2.05/0.65    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 2.05/0.65    inference(negated_conjecture,[],[f23])).
% 2.05/0.65  fof(f23,conjecture,(
% 2.05/0.65    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 2.05/0.65  fof(f989,plain,(
% 2.05/0.65    sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~r2_hidden(sK1,sK0)),
% 2.05/0.65    inference(resolution,[],[f691,f116])).
% 2.05/0.65  fof(f116,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 | ~r2_hidden(X0,X1)) )),
% 2.05/0.65    inference(resolution,[],[f80,f55])).
% 2.05/0.65  fof(f55,plain,(
% 2.05/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f32])).
% 2.05/0.65  fof(f32,plain,(
% 2.05/0.65    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 2.05/0.65    inference(flattening,[],[f31])).
% 2.05/0.65  fof(f31,plain,(
% 2.05/0.65    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 2.05/0.65    inference(ennf_transformation,[],[f27])).
% 2.05/0.65  fof(f27,plain,(
% 2.05/0.65    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 2.05/0.65    inference(unused_predicate_definition_removal,[],[f1])).
% 2.05/0.65  fof(f1,axiom,(
% 2.05/0.65    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 2.05/0.65  fof(f80,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.05/0.65    inference(definition_unfolding,[],[f56,f73])).
% 2.05/0.65  fof(f56,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f33])).
% 2.05/0.65  fof(f33,plain,(
% 2.05/0.65    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 2.05/0.65    inference(ennf_transformation,[],[f26])).
% 2.05/0.65  fof(f26,plain,(
% 2.05/0.65    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 2.05/0.65    inference(unused_predicate_definition_removal,[],[f19])).
% 2.05/0.65  fof(f19,axiom,(
% 2.05/0.65    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.05/0.65  fof(f691,plain,(
% 2.05/0.65    ~r2_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)),
% 2.05/0.65    inference(superposition,[],[f109,f273])).
% 2.05/0.65  fof(f273,plain,(
% 2.05/0.65    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 2.05/0.65    inference(forward_demodulation,[],[f272,f44])).
% 2.05/0.65  fof(f44,plain,(
% 2.05/0.65    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.05/0.65    inference(cnf_transformation,[],[f4])).
% 2.05/0.65  fof(f4,axiom,(
% 2.05/0.65    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.05/0.65  fof(f272,plain,(
% 2.05/0.65    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)),
% 2.05/0.65    inference(forward_demodulation,[],[f258,f106])).
% 2.05/0.65  fof(f106,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.05/0.65    inference(backward_demodulation,[],[f84,f100])).
% 2.05/0.65  fof(f100,plain,(
% 2.05/0.65    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.05/0.65    inference(forward_demodulation,[],[f93,f44])).
% 2.05/0.65  fof(f93,plain,(
% 2.05/0.65    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 2.05/0.65    inference(superposition,[],[f84,f42])).
% 2.05/0.65  fof(f42,plain,(
% 2.05/0.65    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f10])).
% 2.05/0.65  fof(f10,axiom,(
% 2.05/0.65    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.05/0.65  fof(f84,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 2.05/0.65    inference(superposition,[],[f59,f42])).
% 2.05/0.65  fof(f59,plain,(
% 2.05/0.65    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.05/0.65    inference(cnf_transformation,[],[f9])).
% 2.05/0.65  fof(f9,axiom,(
% 2.05/0.65    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.05/0.65  fof(f258,plain,(
% 2.05/0.65    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)))),
% 2.05/0.65    inference(superposition,[],[f142,f42])).
% 2.05/0.65  fof(f142,plain,(
% 2.05/0.65    ( ! [X0] : (k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),X0)))) = X0) )),
% 2.05/0.65    inference(forward_demodulation,[],[f141,f100])).
% 2.05/0.65  fof(f141,plain,(
% 2.05/0.65    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),X0))))) )),
% 2.05/0.65    inference(forward_demodulation,[],[f140,f59])).
% 2.05/0.65  fof(f140,plain,(
% 2.05/0.65    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),X0)))) )),
% 2.05/0.65    inference(forward_demodulation,[],[f138,f59])).
% 2.05/0.65  fof(f138,plain,(
% 2.05/0.65    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),X0))) )),
% 2.05/0.65    inference(superposition,[],[f59,f122])).
% 2.05/0.65  fof(f122,plain,(
% 2.05/0.65    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))))),
% 2.05/0.65    inference(forward_demodulation,[],[f75,f59])).
% 2.05/0.65  fof(f75,plain,(
% 2.05/0.65    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))))),
% 2.05/0.65    inference(definition_unfolding,[],[f39,f72,f73])).
% 2.05/0.65  fof(f72,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 2.05/0.65    inference(definition_unfolding,[],[f52,f71])).
% 2.05/0.65  fof(f71,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.05/0.65    inference(definition_unfolding,[],[f53,f70])).
% 2.05/0.65  fof(f70,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.05/0.65    inference(definition_unfolding,[],[f50,f69])).
% 2.05/0.65  fof(f50,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.05/0.65    inference(cnf_transformation,[],[f21])).
% 2.05/0.65  fof(f21,axiom,(
% 2.05/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.05/0.65  fof(f53,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.05/0.65    inference(cnf_transformation,[],[f11])).
% 2.05/0.65  fof(f11,axiom,(
% 2.05/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.05/0.65  fof(f52,plain,(
% 2.05/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.05/0.65    inference(cnf_transformation,[],[f3])).
% 2.05/0.65  fof(f3,axiom,(
% 2.05/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.05/0.65  fof(f39,plain,(
% 2.05/0.65    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 2.05/0.65    inference(cnf_transformation,[],[f38])).
% 2.05/0.65  fof(f109,plain,(
% 2.05/0.65    ( ! [X2,X3] : (~r2_xboole_0(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),X2)) )),
% 2.05/0.65    inference(resolution,[],[f78,f57])).
% 2.05/0.65  fof(f57,plain,(
% 2.05/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f34])).
% 2.05/0.65  fof(f34,plain,(
% 2.05/0.65    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 2.05/0.65    inference(ennf_transformation,[],[f5])).
% 2.05/0.65  fof(f5,axiom,(
% 2.05/0.65    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).
% 2.05/0.65  fof(f78,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.05/0.65    inference(definition_unfolding,[],[f49,f70])).
% 2.05/0.65  fof(f49,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.05/0.65    inference(cnf_transformation,[],[f8])).
% 2.05/0.65  fof(f8,axiom,(
% 2.05/0.65    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.05/0.65  fof(f993,plain,(
% 2.05/0.65    ( ! [X0] : (r2_hidden(sK1,X0) | r1_xboole_0(sK0,X0)) )),
% 2.05/0.65    inference(resolution,[],[f692,f112])).
% 2.05/0.65  fof(f112,plain,(
% 2.05/0.65    ( ! [X2,X3,X1] : (~r1_tarski(X3,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | r1_xboole_0(X3,X2) | r2_hidden(X1,X2)) )),
% 2.05/0.65    inference(resolution,[],[f79,f60])).
% 2.05/0.65  fof(f60,plain,(
% 2.05/0.65    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f36])).
% 2.05/0.65  fof(f36,plain,(
% 2.05/0.65    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.05/0.65    inference(flattening,[],[f35])).
% 2.05/0.65  fof(f35,plain,(
% 2.05/0.65    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.05/0.65    inference(ennf_transformation,[],[f6])).
% 2.05/0.65  fof(f6,axiom,(
% 2.05/0.65    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 2.05/0.65  fof(f79,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.05/0.65    inference(definition_unfolding,[],[f54,f73])).
% 2.05/0.65  fof(f54,plain,(
% 2.05/0.65    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.05/0.65    inference(cnf_transformation,[],[f30])).
% 2.05/0.65  fof(f30,plain,(
% 2.05/0.65    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.05/0.65    inference(ennf_transformation,[],[f20])).
% 2.05/0.65  fof(f20,axiom,(
% 2.05/0.65    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.05/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.05/0.65  fof(f692,plain,(
% 2.05/0.65    r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.05/0.65    inference(superposition,[],[f78,f273])).
% 2.05/0.65  fof(f40,plain,(
% 2.05/0.65    k1_xboole_0 != sK0),
% 2.05/0.65    inference(cnf_transformation,[],[f38])).
% 2.05/0.65  % SZS output end Proof for theBenchmark
% 2.05/0.65  % (15822)------------------------------
% 2.05/0.65  % (15822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.65  % (15822)Termination reason: Refutation
% 2.05/0.65  
% 2.05/0.65  % (15822)Memory used [KB]: 2558
% 2.05/0.65  % (15822)Time elapsed: 0.214 s
% 2.05/0.65  % (15822)------------------------------
% 2.05/0.65  % (15822)------------------------------
% 2.05/0.65  % (15791)Success in time 0.27 s
%------------------------------------------------------------------------------
