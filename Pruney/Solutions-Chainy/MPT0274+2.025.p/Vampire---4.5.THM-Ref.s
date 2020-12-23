%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:23 EST 2020

% Result     : Theorem 8.75s
% Output     : Refutation 8.75s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 853 expanded)
%              Number of leaves         :   20 ( 258 expanded)
%              Depth                    :   24
%              Number of atoms          :  257 (1434 expanded)
%              Number of equality atoms :   98 ( 779 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9646,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f8415,f8470,f8458,f8517,f1069])).

fof(f1069,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(trivial_inequality_removal,[],[f1058])).

fof(f1058,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(superposition,[],[f385,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f69,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f66])).

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

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f385,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f382,f37])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f382,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(backward_demodulation,[],[f83,f379])).

fof(f379,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f350,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f350,plain,(
    ! [X0,X1] : k3_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f47,f35])).

fof(f35,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f47,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f83,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(backward_demodulation,[],[f72,f36])).

fof(f72,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f30,f69,f39,f69])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f30,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f8517,plain,(
    ! [X0,X1] : r2_hidden(sK0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0,X1))) ),
    inference(forward_demodulation,[],[f8486,f37])).

fof(f8486,plain,(
    ! [X0,X1] : r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0,X1),sK2)) ),
    inference(unit_resulting_resolution,[],[f859,f8470,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f859,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(unit_resulting_resolution,[],[f82,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | ~ sP5(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f58,f68])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f82,plain,(
    ! [X4,X2,X1] : sP5(X4,X2,X1,X4) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( X0 != X4
      | sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8458,plain,(
    ! [X0,X1] : r2_hidden(sK1,k5_xboole_0(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK1))) ),
    inference(forward_demodulation,[],[f8423,f37])).

fof(f8423,plain,(
    ! [X0,X1] : r2_hidden(sK1,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK1),sK2)) ),
    inference(unit_resulting_resolution,[],[f857,f8415,f52])).

fof(f857,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
    inference(unit_resulting_resolution,[],[f80,f79])).

fof(f80,plain,(
    ! [X4,X0,X1] : sP5(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8470,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f8464])).

fof(f8464,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f8406,f81])).

fof(f81,plain,(
    ! [X4,X2,X0] : sP5(X4,X2,X4,X0) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8406,plain,(
    ! [X25] :
      ( ~ sP5(X25,sK1,sK0,sK0)
      | ~ r2_hidden(X25,sK2)
      | ~ r2_hidden(sK0,sK2) ) ),
    inference(resolution,[],[f861,f3241])).

fof(f3241,plain,
    ( r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f3233])).

fof(f3233,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK0,sK2) ),
    inference(superposition,[],[f43,f3188])).

fof(f3188,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f3187,f86])).

fof(f86,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f37,f34])).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f3187,plain,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f3186,f2206])).

fof(f2206,plain,(
    ! [X78,X76,X77] : k3_xboole_0(k5_xboole_0(X76,X77),X78) = k3_xboole_0(k5_xboole_0(X77,X76),X78) ),
    inference(global_subsumption,[],[f219,f2173])).

fof(f2173,plain,(
    ! [X78,X76,X77] :
      ( k3_xboole_0(k5_xboole_0(X76,X77),X78) = k3_xboole_0(k5_xboole_0(X77,X76),X78)
      | ~ r1_xboole_0(k1_xboole_0,X78) ) ),
    inference(superposition,[],[f387,f531])).

fof(f531,plain,(
    ! [X43,X42] : k5_xboole_0(X43,X42) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X42,X43)) ),
    inference(superposition,[],[f145,f86])).

fof(f145,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f46,f37])).

fof(f46,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f387,plain,(
    ! [X6,X7,X5] :
      ( k3_xboole_0(X7,X6) = k3_xboole_0(k5_xboole_0(X5,X7),X6)
      | ~ r1_xboole_0(X5,X6) ) ),
    inference(forward_demodulation,[],[f352,f86])).

fof(f352,plain,(
    ! [X6,X7,X5] :
      ( k3_xboole_0(k5_xboole_0(X5,X7),X6) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X7,X6))
      | ~ r1_xboole_0(X5,X6) ) ),
    inference(superposition,[],[f47,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f219,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(global_subsumption,[],[f163,f217])).

fof(f217,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(k1_xboole_0,X0),X1)
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f216,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f216,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f206])).

fof(f206,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f50,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f163,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k1_xboole_0,X0),X1)
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f162,f41])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,X0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f49,f33])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3186,plain,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK2,k1_xboole_0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f3185,f36])).

fof(f3185,plain,
    ( k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k1_xboole_0))
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f3184,f33])).

fof(f3184,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f3113,f145])).

fof(f3113,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | ~ r2_hidden(sK0,sK2) ),
    inference(superposition,[],[f867,f384])).

fof(f384,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f381,f37])).

fof(f381,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))
    | ~ r2_hidden(sK0,sK2) ),
    inference(backward_demodulation,[],[f84,f379])).

fof(f84,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK0,sK2) ),
    inference(backward_demodulation,[],[f71,f36])).

fof(f71,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f31,f69,f39,f69])).

fof(f31,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f867,plain,(
    ! [X6,X5] : k3_xboole_0(X6,k5_xboole_0(X6,X5)) = k5_xboole_0(X6,k3_xboole_0(X6,X5)) ),
    inference(superposition,[],[f379,f36])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f861,plain,(
    ! [X6,X4,X8,X7,X5] :
      ( ~ r1_xboole_0(X8,k6_enumset1(X7,X7,X7,X7,X7,X7,X6,X5))
      | ~ r2_hidden(X4,X8)
      | ~ sP5(X4,X5,X6,X7) ) ),
    inference(resolution,[],[f79,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8415,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f8409])).

fof(f8409,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f8405,f80])).

fof(f8405,plain,(
    ! [X24] :
      ( ~ sP5(X24,sK1,sK0,sK0)
      | ~ r2_hidden(X24,sK2)
      | ~ r2_hidden(sK1,sK2) ) ),
    inference(resolution,[],[f861,f3266])).

fof(f3266,plain,
    ( r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK1,sK2) ),
    inference(trivial_inequality_removal,[],[f3258])).

fof(f3258,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK1,sK2) ),
    inference(superposition,[],[f43,f3193])).

fof(f3193,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f3192,f86])).

fof(f3192,plain,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f3191,f2206])).

fof(f3191,plain,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK2,k1_xboole_0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f3190,f36])).

fof(f3190,plain,
    ( k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k1_xboole_0))
    | ~ r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f3189,f33])).

fof(f3189,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | ~ r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f3114,f145])).

fof(f3114,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | ~ r2_hidden(sK1,sK2) ),
    inference(superposition,[],[f867,f383])).

fof(f383,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f380,f37])).

fof(f380,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))
    | ~ r2_hidden(sK1,sK2) ),
    inference(backward_demodulation,[],[f85,f379])).

fof(f85,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ r2_hidden(sK1,sK2) ),
    inference(backward_demodulation,[],[f70,f36])).

fof(f70,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f32,f69,f39,f69])).

fof(f32,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:26:46 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.51  % (14701)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (14703)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (14698)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (14716)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (14694)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (14708)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (14699)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (14704)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.26/0.53  % (14705)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.26/0.53  % (14717)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.26/0.53  % (14709)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.26/0.53  % (14722)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.26/0.53  % (14706)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.53  % (14700)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.26/0.54  % (14695)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.26/0.54  % (14714)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.26/0.54  % (14715)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.26/0.54  % (14697)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.26/0.54  % (14718)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.26/0.54  % (14723)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.26/0.54  % (14696)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.26/0.55  % (14696)Refutation not found, incomplete strategy% (14696)------------------------------
% 1.26/0.55  % (14696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.55  % (14696)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.55  
% 1.26/0.55  % (14696)Memory used [KB]: 10746
% 1.26/0.55  % (14696)Time elapsed: 0.128 s
% 1.26/0.55  % (14696)------------------------------
% 1.26/0.55  % (14696)------------------------------
% 1.26/0.55  % (14719)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.26/0.55  % (14721)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.55  % (14720)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.55  % (14710)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.56  % (14713)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.56  % (14712)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.56  % (14711)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.56  % (14702)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.56  % (14711)Refutation not found, incomplete strategy% (14711)------------------------------
% 1.40/0.56  % (14711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (14711)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (14711)Memory used [KB]: 10746
% 1.40/0.56  % (14711)Time elapsed: 0.149 s
% 1.40/0.56  % (14711)------------------------------
% 1.40/0.56  % (14711)------------------------------
% 1.40/0.56  % (14702)Refutation not found, incomplete strategy% (14702)------------------------------
% 1.40/0.56  % (14702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (14702)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (14702)Memory used [KB]: 10618
% 1.40/0.56  % (14702)Time elapsed: 0.150 s
% 1.40/0.56  % (14702)------------------------------
% 1.40/0.56  % (14702)------------------------------
% 1.40/0.56  % (14707)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.37/0.69  % (14764)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.37/0.71  % (14771)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.37/0.73  % (14773)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.33/0.84  % (14699)Time limit reached!
% 3.33/0.84  % (14699)------------------------------
% 3.33/0.84  % (14699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.33/0.84  % (14699)Termination reason: Time limit
% 3.33/0.84  % (14699)Termination phase: Saturation
% 3.33/0.84  
% 3.33/0.84  % (14699)Memory used [KB]: 10362
% 3.33/0.84  % (14699)Time elapsed: 0.400 s
% 3.33/0.84  % (14699)------------------------------
% 3.33/0.84  % (14699)------------------------------
% 3.59/0.91  % (14706)Time limit reached!
% 3.59/0.91  % (14706)------------------------------
% 3.59/0.91  % (14706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.59/0.93  % (14706)Termination reason: Time limit
% 3.59/0.93  % (14706)Termination phase: Saturation
% 3.59/0.93  
% 3.59/0.93  % (14706)Memory used [KB]: 9594
% 3.59/0.93  % (14706)Time elapsed: 0.500 s
% 3.59/0.93  % (14706)------------------------------
% 3.59/0.93  % (14706)------------------------------
% 4.17/0.94  % (14704)Time limit reached!
% 4.17/0.94  % (14704)------------------------------
% 4.17/0.94  % (14704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/0.94  % (14704)Termination reason: Time limit
% 4.17/0.94  
% 4.17/0.94  % (14704)Memory used [KB]: 15607
% 4.17/0.94  % (14704)Time elapsed: 0.519 s
% 4.17/0.94  % (14704)------------------------------
% 4.17/0.94  % (14704)------------------------------
% 4.17/0.95  % (14694)Time limit reached!
% 4.17/0.95  % (14694)------------------------------
% 4.17/0.95  % (14694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/0.95  % (14694)Termination reason: Time limit
% 4.17/0.95  
% 4.17/0.95  % (14694)Memory used [KB]: 2430
% 4.17/0.95  % (14694)Time elapsed: 0.527 s
% 4.17/0.95  % (14694)------------------------------
% 4.17/0.95  % (14694)------------------------------
% 4.17/0.95  % (14695)Time limit reached!
% 4.17/0.95  % (14695)------------------------------
% 4.17/0.95  % (14695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/0.95  % (14695)Termination reason: Time limit
% 4.17/0.95  % (14695)Termination phase: Saturation
% 4.17/0.95  
% 4.17/0.95  % (14695)Memory used [KB]: 8571
% 4.17/0.95  % (14695)Time elapsed: 0.500 s
% 4.17/0.95  % (14695)------------------------------
% 4.17/0.95  % (14695)------------------------------
% 4.49/0.98  % (14891)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.49/1.02  % (14710)Time limit reached!
% 4.49/1.02  % (14710)------------------------------
% 4.49/1.02  % (14710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.49/1.02  % (14710)Termination reason: Time limit
% 4.49/1.02  % (14710)Termination phase: Saturation
% 4.49/1.02  
% 4.49/1.02  % (14710)Memory used [KB]: 17398
% 4.49/1.02  % (14710)Time elapsed: 0.600 s
% 4.49/1.02  % (14710)------------------------------
% 4.49/1.02  % (14710)------------------------------
% 4.49/1.02  % (14916)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.85/1.05  % (14923)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.85/1.06  % (14917)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.48/1.08  % (14701)Time limit reached!
% 5.48/1.08  % (14701)------------------------------
% 5.48/1.08  % (14701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.48/1.08  % (14701)Termination reason: Time limit
% 5.48/1.08  % (14701)Termination phase: Saturation
% 5.48/1.08  
% 5.48/1.08  % (14701)Memory used [KB]: 12409
% 5.48/1.08  % (14701)Time elapsed: 0.600 s
% 5.48/1.08  % (14701)------------------------------
% 5.48/1.08  % (14701)------------------------------
% 5.48/1.08  % (14928)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.48/1.11  % (14722)Time limit reached!
% 5.48/1.11  % (14722)------------------------------
% 5.48/1.11  % (14722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.48/1.11  % (14722)Termination reason: Time limit
% 5.48/1.11  % (14722)Termination phase: Saturation
% 5.48/1.11  
% 5.48/1.11  % (14722)Memory used [KB]: 9466
% 5.48/1.11  % (14722)Time elapsed: 0.600 s
% 5.48/1.11  % (14722)------------------------------
% 5.48/1.11  % (14722)------------------------------
% 5.97/1.13  % (14959)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.97/1.13  % (14959)Refutation not found, incomplete strategy% (14959)------------------------------
% 5.97/1.13  % (14959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.97/1.13  % (14959)Termination reason: Refutation not found, incomplete strategy
% 5.97/1.13  
% 5.97/1.13  % (14959)Memory used [KB]: 1791
% 5.97/1.13  % (14959)Time elapsed: 0.062 s
% 5.97/1.13  % (14959)------------------------------
% 5.97/1.13  % (14959)------------------------------
% 6.24/1.20  % (14960)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.24/1.22  % (14715)Time limit reached!
% 6.24/1.22  % (14715)------------------------------
% 6.24/1.22  % (14715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.24/1.22  % (14715)Termination reason: Time limit
% 6.24/1.22  
% 6.24/1.22  % (14715)Memory used [KB]: 3454
% 6.24/1.22  % (14715)Time elapsed: 0.813 s
% 6.24/1.22  % (14715)------------------------------
% 6.24/1.22  % (14715)------------------------------
% 6.76/1.24  % (14961)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.76/1.24  % (14962)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 7.01/1.30  % (14891)Time limit reached!
% 7.01/1.30  % (14891)------------------------------
% 7.01/1.30  % (14891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.01/1.30  % (14891)Termination reason: Time limit
% 7.01/1.30  % (14891)Termination phase: Saturation
% 7.01/1.30  
% 7.01/1.30  % (14891)Memory used [KB]: 8443
% 7.01/1.30  % (14891)Time elapsed: 0.400 s
% 7.01/1.30  % (14891)------------------------------
% 7.01/1.30  % (14891)------------------------------
% 7.63/1.37  % (14963)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 7.63/1.39  % (14916)Time limit reached!
% 7.63/1.39  % (14916)------------------------------
% 7.63/1.39  % (14916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.63/1.39  % (14916)Termination reason: Time limit
% 7.63/1.39  % (14916)Termination phase: Saturation
% 7.63/1.39  
% 7.63/1.39  % (14916)Memory used [KB]: 15607
% 7.63/1.39  % (14916)Time elapsed: 0.400 s
% 7.63/1.39  % (14916)------------------------------
% 7.63/1.39  % (14916)------------------------------
% 8.03/1.44  % (14964)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 8.03/1.44  % (14964)Refutation not found, incomplete strategy% (14964)------------------------------
% 8.03/1.44  % (14964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.03/1.44  % (14964)Termination reason: Refutation not found, incomplete strategy
% 8.03/1.44  
% 8.03/1.44  % (14964)Memory used [KB]: 1663
% 8.03/1.44  % (14964)Time elapsed: 0.119 s
% 8.03/1.44  % (14964)------------------------------
% 8.03/1.44  % (14964)------------------------------
% 8.34/1.50  % (14965)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 8.75/1.56  % (14718)Refutation found. Thanks to Tanya!
% 8.75/1.56  % SZS status Theorem for theBenchmark
% 8.75/1.56  % SZS output start Proof for theBenchmark
% 8.75/1.56  fof(f9646,plain,(
% 8.75/1.56    $false),
% 8.75/1.56    inference(unit_resulting_resolution,[],[f8415,f8470,f8458,f8517,f1069])).
% 8.75/1.56  fof(f1069,plain,(
% 8.75/1.56    ~r2_hidden(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | ~r2_hidden(sK0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 8.75/1.56    inference(trivial_inequality_removal,[],[f1058])).
% 8.75/1.56  fof(f1058,plain,(
% 8.75/1.56    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | ~r2_hidden(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 8.75/1.56    inference(superposition,[],[f385,f73])).
% 8.75/1.56  fof(f73,plain,(
% 8.75/1.56    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 8.75/1.56    inference(definition_unfolding,[],[f48,f69,f69])).
% 8.75/1.56  fof(f69,plain,(
% 8.75/1.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 8.75/1.56    inference(definition_unfolding,[],[f38,f68])).
% 8.75/1.56  fof(f68,plain,(
% 8.75/1.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 8.75/1.56    inference(definition_unfolding,[],[f45,f67])).
% 8.75/1.56  fof(f67,plain,(
% 8.75/1.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 8.75/1.56    inference(definition_unfolding,[],[f53,f66])).
% 8.75/1.56  fof(f66,plain,(
% 8.75/1.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 8.75/1.56    inference(definition_unfolding,[],[f62,f65])).
% 8.75/1.56  fof(f65,plain,(
% 8.75/1.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 8.75/1.56    inference(definition_unfolding,[],[f63,f64])).
% 8.75/1.56  fof(f64,plain,(
% 8.75/1.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f18])).
% 8.75/1.56  fof(f18,axiom,(
% 8.75/1.56    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 8.75/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 8.75/1.56  fof(f63,plain,(
% 8.75/1.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f17])).
% 8.75/1.56  fof(f17,axiom,(
% 8.75/1.56    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 8.75/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 8.75/1.56  fof(f62,plain,(
% 8.75/1.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f16])).
% 8.75/1.56  fof(f16,axiom,(
% 8.75/1.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 8.75/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 8.75/1.56  fof(f53,plain,(
% 8.75/1.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f15])).
% 8.75/1.56  fof(f15,axiom,(
% 8.75/1.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 8.75/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 8.75/1.56  fof(f45,plain,(
% 8.75/1.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f14])).
% 8.75/1.56  fof(f14,axiom,(
% 8.75/1.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 8.75/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 8.75/1.56  fof(f38,plain,(
% 8.75/1.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f13])).
% 8.75/1.56  fof(f13,axiom,(
% 8.75/1.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 8.75/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 8.75/1.56  fof(f48,plain,(
% 8.75/1.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X2,X1) | k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f27])).
% 8.75/1.56  fof(f27,plain,(
% 8.75/1.56    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 8.75/1.56    inference(flattening,[],[f26])).
% 8.75/1.56  fof(f26,plain,(
% 8.75/1.56    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 8.75/1.56    inference(ennf_transformation,[],[f19])).
% 8.75/1.56  fof(f19,axiom,(
% 8.75/1.56    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 8.75/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 8.75/1.56  fof(f385,plain,(
% 8.75/1.56    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2)),
% 8.75/1.56    inference(forward_demodulation,[],[f382,f37])).
% 8.75/1.56  fof(f37,plain,(
% 8.75/1.56    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f2])).
% 8.75/1.56  fof(f2,axiom,(
% 8.75/1.56    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 8.75/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 8.75/1.56  fof(f382,plain,(
% 8.75/1.56    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2)),
% 8.75/1.56    inference(backward_demodulation,[],[f83,f379])).
% 8.75/1.56  fof(f379,plain,(
% 8.75/1.56    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 8.75/1.56    inference(forward_demodulation,[],[f350,f36])).
% 8.75/1.56  fof(f36,plain,(
% 8.75/1.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f1])).
% 8.75/1.56  fof(f1,axiom,(
% 8.75/1.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 8.75/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 8.75/1.56  fof(f350,plain,(
% 8.75/1.56    ( ! [X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 8.75/1.56    inference(superposition,[],[f47,f35])).
% 8.75/1.56  fof(f35,plain,(
% 8.75/1.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 8.75/1.56    inference(cnf_transformation,[],[f22])).
% 8.75/1.56  fof(f22,plain,(
% 8.75/1.56    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 8.75/1.56    inference(rectify,[],[f4])).
% 8.75/1.56  fof(f4,axiom,(
% 8.75/1.56    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 8.75/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 8.75/1.56  fof(f47,plain,(
% 8.75/1.56    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f8])).
% 8.75/1.56  fof(f8,axiom,(
% 8.75/1.56    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 8.75/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 8.75/1.56  fof(f83,plain,(
% 8.75/1.56    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2)),
% 8.75/1.56    inference(backward_demodulation,[],[f72,f36])).
% 8.75/1.56  fof(f72,plain,(
% 8.75/1.56    r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))),
% 8.75/1.56    inference(definition_unfolding,[],[f30,f69,f39,f69])).
% 8.75/1.56  fof(f39,plain,(
% 8.75/1.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.75/1.56    inference(cnf_transformation,[],[f7])).
% 8.75/1.56  fof(f7,axiom,(
% 8.75/1.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.75/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 8.75/1.56  fof(f30,plain,(
% 8.75/1.56    r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 8.75/1.56    inference(cnf_transformation,[],[f24])).
% 8.75/1.56  fof(f24,plain,(
% 8.75/1.56    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 8.75/1.56    inference(ennf_transformation,[],[f21])).
% 8.75/1.56  fof(f21,negated_conjecture,(
% 8.75/1.56    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 8.75/1.56    inference(negated_conjecture,[],[f20])).
% 8.75/1.56  fof(f20,conjecture,(
% 8.75/1.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 8.75/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 8.75/1.56  fof(f8517,plain,(
% 8.75/1.56    ( ! [X0,X1] : (r2_hidden(sK0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0,X1)))) )),
% 8.75/1.56    inference(forward_demodulation,[],[f8486,f37])).
% 8.75/1.56  fof(f8486,plain,(
% 8.75/1.56    ( ! [X0,X1] : (r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0,X1),sK2))) )),
% 8.75/1.56    inference(unit_resulting_resolution,[],[f859,f8470,f52])).
% 8.75/1.56  fof(f52,plain,(
% 8.75/1.56    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f28])).
% 8.75/1.56  fof(f28,plain,(
% 8.75/1.56    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 8.75/1.56    inference(ennf_transformation,[],[f5])).
% 8.75/1.56  fof(f5,axiom,(
% 8.75/1.56    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 8.75/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 8.75/1.56  fof(f859,plain,(
% 8.75/1.56    ( ! [X2,X0,X1] : (r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 8.75/1.56    inference(unit_resulting_resolution,[],[f82,f79])).
% 8.75/1.56  fof(f79,plain,(
% 8.75/1.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | ~sP5(X4,X2,X1,X0)) )),
% 8.75/1.56    inference(equality_resolution,[],[f77])).
% 8.75/1.56  fof(f77,plain,(
% 8.75/1.56    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 8.75/1.56    inference(definition_unfolding,[],[f58,f68])).
% 8.75/1.56  fof(f58,plain,(
% 8.75/1.56    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 8.75/1.56    inference(cnf_transformation,[],[f29])).
% 8.75/1.56  fof(f29,plain,(
% 8.75/1.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 8.75/1.56    inference(ennf_transformation,[],[f12])).
% 8.75/1.56  fof(f12,axiom,(
% 8.75/1.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 8.75/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 8.75/1.56  fof(f82,plain,(
% 8.75/1.56    ( ! [X4,X2,X1] : (sP5(X4,X2,X1,X4)) )),
% 8.75/1.56    inference(equality_resolution,[],[f54])).
% 8.75/1.56  fof(f54,plain,(
% 8.75/1.56    ( ! [X4,X2,X0,X1] : (X0 != X4 | sP5(X4,X2,X1,X0)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f29])).
% 8.75/1.56  fof(f8458,plain,(
% 8.75/1.56    ( ! [X0,X1] : (r2_hidden(sK1,k5_xboole_0(sK2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK1)))) )),
% 8.75/1.56    inference(forward_demodulation,[],[f8423,f37])).
% 8.75/1.56  fof(f8423,plain,(
% 8.75/1.56    ( ! [X0,X1] : (r2_hidden(sK1,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK1),sK2))) )),
% 8.75/1.56    inference(unit_resulting_resolution,[],[f857,f8415,f52])).
% 8.75/1.56  fof(f857,plain,(
% 8.75/1.56    ( ! [X2,X0,X1] : (r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))) )),
% 8.75/1.56    inference(unit_resulting_resolution,[],[f80,f79])).
% 8.75/1.56  fof(f80,plain,(
% 8.75/1.56    ( ! [X4,X0,X1] : (sP5(X4,X4,X1,X0)) )),
% 8.75/1.56    inference(equality_resolution,[],[f56])).
% 8.75/1.56  fof(f56,plain,(
% 8.75/1.56    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP5(X4,X2,X1,X0)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f29])).
% 8.75/1.56  fof(f8470,plain,(
% 8.75/1.56    ~r2_hidden(sK0,sK2)),
% 8.75/1.56    inference(duplicate_literal_removal,[],[f8464])).
% 8.75/1.56  fof(f8464,plain,(
% 8.75/1.56    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK0,sK2)),
% 8.75/1.56    inference(resolution,[],[f8406,f81])).
% 8.75/1.56  fof(f81,plain,(
% 8.75/1.56    ( ! [X4,X2,X0] : (sP5(X4,X2,X4,X0)) )),
% 8.75/1.56    inference(equality_resolution,[],[f55])).
% 8.75/1.56  fof(f55,plain,(
% 8.75/1.56    ( ! [X4,X2,X0,X1] : (X1 != X4 | sP5(X4,X2,X1,X0)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f29])).
% 8.75/1.56  fof(f8406,plain,(
% 8.75/1.56    ( ! [X25] : (~sP5(X25,sK1,sK0,sK0) | ~r2_hidden(X25,sK2) | ~r2_hidden(sK0,sK2)) )),
% 8.75/1.56    inference(resolution,[],[f861,f3241])).
% 8.75/1.56  fof(f3241,plain,(
% 8.75/1.56    r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK0,sK2)),
% 8.75/1.56    inference(trivial_inequality_removal,[],[f3233])).
% 8.75/1.56  fof(f3233,plain,(
% 8.75/1.56    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK0,sK2)),
% 8.75/1.56    inference(superposition,[],[f43,f3188])).
% 8.75/1.56  fof(f3188,plain,(
% 8.75/1.56    k1_xboole_0 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK0,sK2)),
% 8.75/1.56    inference(forward_demodulation,[],[f3187,f86])).
% 8.75/1.56  fof(f86,plain,(
% 8.75/1.56    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 8.75/1.56    inference(superposition,[],[f37,f34])).
% 8.75/1.56  fof(f34,plain,(
% 8.75/1.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.75/1.56    inference(cnf_transformation,[],[f9])).
% 8.75/1.56  fof(f9,axiom,(
% 8.75/1.56    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 8.75/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 8.75/1.56  fof(f3187,plain,(
% 8.75/1.56    k1_xboole_0 = k3_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK0,sK2)),
% 8.75/1.56    inference(forward_demodulation,[],[f3186,f2206])).
% 8.75/1.56  fof(f2206,plain,(
% 8.75/1.56    ( ! [X78,X76,X77] : (k3_xboole_0(k5_xboole_0(X76,X77),X78) = k3_xboole_0(k5_xboole_0(X77,X76),X78)) )),
% 8.75/1.56    inference(global_subsumption,[],[f219,f2173])).
% 8.75/1.56  fof(f2173,plain,(
% 8.75/1.56    ( ! [X78,X76,X77] : (k3_xboole_0(k5_xboole_0(X76,X77),X78) = k3_xboole_0(k5_xboole_0(X77,X76),X78) | ~r1_xboole_0(k1_xboole_0,X78)) )),
% 8.75/1.56    inference(superposition,[],[f387,f531])).
% 8.75/1.56  fof(f531,plain,(
% 8.75/1.56    ( ! [X43,X42] : (k5_xboole_0(X43,X42) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X42,X43))) )),
% 8.75/1.56    inference(superposition,[],[f145,f86])).
% 8.75/1.56  fof(f145,plain,(
% 8.75/1.56    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8))) )),
% 8.75/1.56    inference(superposition,[],[f46,f37])).
% 8.75/1.56  fof(f46,plain,(
% 8.75/1.56    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 8.75/1.56    inference(cnf_transformation,[],[f10])).
% 8.75/1.56  fof(f10,axiom,(
% 8.75/1.56    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 8.75/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 8.75/1.56  fof(f387,plain,(
% 8.75/1.56    ( ! [X6,X7,X5] : (k3_xboole_0(X7,X6) = k3_xboole_0(k5_xboole_0(X5,X7),X6) | ~r1_xboole_0(X5,X6)) )),
% 8.75/1.56    inference(forward_demodulation,[],[f352,f86])).
% 8.75/1.56  fof(f352,plain,(
% 8.75/1.56    ( ! [X6,X7,X5] : (k3_xboole_0(k5_xboole_0(X5,X7),X6) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X7,X6)) | ~r1_xboole_0(X5,X6)) )),
% 8.75/1.56    inference(superposition,[],[f47,f44])).
% 8.75/1.56  fof(f44,plain,(
% 8.75/1.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f3])).
% 8.75/1.56  fof(f3,axiom,(
% 8.75/1.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 8.75/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 8.75/1.56  fof(f219,plain,(
% 8.75/1.56    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 8.75/1.56    inference(global_subsumption,[],[f163,f217])).
% 8.75/1.56  fof(f217,plain,(
% 8.75/1.56    ( ! [X0,X1] : (~r2_hidden(sK3(k1_xboole_0,X0),X1) | r1_xboole_0(k1_xboole_0,X0)) )),
% 8.75/1.56    inference(resolution,[],[f216,f41])).
% 8.75/1.56  fof(f41,plain,(
% 8.75/1.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f25])).
% 8.75/1.56  fof(f25,plain,(
% 8.75/1.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 8.75/1.56    inference(ennf_transformation,[],[f23])).
% 8.75/1.56  fof(f23,plain,(
% 8.75/1.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 8.75/1.56    inference(rectify,[],[f6])).
% 8.75/1.56  fof(f6,axiom,(
% 8.75/1.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 8.75/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 8.75/1.56  fof(f216,plain,(
% 8.75/1.56    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 8.75/1.56    inference(duplicate_literal_removal,[],[f206])).
% 8.75/1.56  fof(f206,plain,(
% 8.75/1.56    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X0)) )),
% 8.75/1.56    inference(superposition,[],[f50,f33])).
% 8.75/1.56  fof(f33,plain,(
% 8.75/1.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f11])).
% 8.75/1.56  fof(f11,axiom,(
% 8.75/1.56    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 8.75/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 8.75/1.56  fof(f50,plain,(
% 8.75/1.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f28])).
% 8.75/1.56  fof(f163,plain,(
% 8.75/1.56    ( ! [X0,X1] : (r2_hidden(sK3(k1_xboole_0,X0),X1) | r1_xboole_0(k1_xboole_0,X0)) )),
% 8.75/1.56    inference(resolution,[],[f162,f41])).
% 8.75/1.56  fof(f162,plain,(
% 8.75/1.56    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X0)) )),
% 8.75/1.56    inference(duplicate_literal_removal,[],[f156])).
% 8.75/1.56  fof(f156,plain,(
% 8.75/1.56    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X0) | r2_hidden(X1,X0)) )),
% 8.75/1.56    inference(superposition,[],[f49,f33])).
% 8.75/1.56  fof(f49,plain,(
% 8.75/1.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f28])).
% 8.75/1.56  fof(f3186,plain,(
% 8.75/1.56    k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK2,k1_xboole_0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK0,sK2)),
% 8.75/1.56    inference(forward_demodulation,[],[f3185,f36])).
% 8.75/1.56  fof(f3185,plain,(
% 8.75/1.56    k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k1_xboole_0)) | ~r2_hidden(sK0,sK2)),
% 8.75/1.56    inference(forward_demodulation,[],[f3184,f33])).
% 8.75/1.56  fof(f3184,plain,(
% 8.75/1.56    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | ~r2_hidden(sK0,sK2)),
% 8.75/1.56    inference(forward_demodulation,[],[f3113,f145])).
% 8.75/1.56  fof(f3113,plain,(
% 8.75/1.56    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | ~r2_hidden(sK0,sK2)),
% 8.75/1.56    inference(superposition,[],[f867,f384])).
% 8.75/1.56  fof(f384,plain,(
% 8.75/1.56    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK0,sK2)),
% 8.75/1.56    inference(forward_demodulation,[],[f381,f37])).
% 8.75/1.56  fof(f381,plain,(
% 8.75/1.56    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) | ~r2_hidden(sK0,sK2)),
% 8.75/1.56    inference(backward_demodulation,[],[f84,f379])).
% 8.75/1.56  fof(f84,plain,(
% 8.75/1.56    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK0,sK2)),
% 8.75/1.56    inference(backward_demodulation,[],[f71,f36])).
% 8.75/1.56  fof(f71,plain,(
% 8.75/1.56    ~r2_hidden(sK0,sK2) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))),
% 8.75/1.56    inference(definition_unfolding,[],[f31,f69,f39,f69])).
% 8.75/1.56  fof(f31,plain,(
% 8.75/1.56    ~r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 8.75/1.56    inference(cnf_transformation,[],[f24])).
% 8.75/1.56  fof(f867,plain,(
% 8.75/1.56    ( ! [X6,X5] : (k3_xboole_0(X6,k5_xboole_0(X6,X5)) = k5_xboole_0(X6,k3_xboole_0(X6,X5))) )),
% 8.75/1.56    inference(superposition,[],[f379,f36])).
% 8.75/1.56  fof(f43,plain,(
% 8.75/1.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f3])).
% 8.75/1.56  fof(f861,plain,(
% 8.75/1.56    ( ! [X6,X4,X8,X7,X5] : (~r1_xboole_0(X8,k6_enumset1(X7,X7,X7,X7,X7,X7,X6,X5)) | ~r2_hidden(X4,X8) | ~sP5(X4,X5,X6,X7)) )),
% 8.75/1.56    inference(resolution,[],[f79,f40])).
% 8.75/1.56  fof(f40,plain,(
% 8.75/1.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 8.75/1.56    inference(cnf_transformation,[],[f25])).
% 8.75/1.56  fof(f8415,plain,(
% 8.75/1.56    ~r2_hidden(sK1,sK2)),
% 8.75/1.56    inference(duplicate_literal_removal,[],[f8409])).
% 8.75/1.56  fof(f8409,plain,(
% 8.75/1.56    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK1,sK2)),
% 8.75/1.56    inference(resolution,[],[f8405,f80])).
% 8.75/1.56  fof(f8405,plain,(
% 8.75/1.56    ( ! [X24] : (~sP5(X24,sK1,sK0,sK0) | ~r2_hidden(X24,sK2) | ~r2_hidden(sK1,sK2)) )),
% 8.75/1.56    inference(resolution,[],[f861,f3266])).
% 8.75/1.56  fof(f3266,plain,(
% 8.75/1.56    r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK1,sK2)),
% 8.75/1.56    inference(trivial_inequality_removal,[],[f3258])).
% 8.75/1.56  fof(f3258,plain,(
% 8.75/1.56    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK1,sK2)),
% 8.75/1.56    inference(superposition,[],[f43,f3193])).
% 8.75/1.56  fof(f3193,plain,(
% 8.75/1.56    k1_xboole_0 = k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK1,sK2)),
% 8.75/1.56    inference(forward_demodulation,[],[f3192,f86])).
% 8.75/1.56  fof(f3192,plain,(
% 8.75/1.56    k1_xboole_0 = k3_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK1,sK2)),
% 8.75/1.56    inference(forward_demodulation,[],[f3191,f2206])).
% 8.75/1.56  fof(f3191,plain,(
% 8.75/1.56    k1_xboole_0 = k3_xboole_0(k5_xboole_0(sK2,k1_xboole_0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK1,sK2)),
% 8.75/1.56    inference(forward_demodulation,[],[f3190,f36])).
% 8.75/1.56  fof(f3190,plain,(
% 8.75/1.56    k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k1_xboole_0)) | ~r2_hidden(sK1,sK2)),
% 8.75/1.56    inference(forward_demodulation,[],[f3189,f33])).
% 8.75/1.56  fof(f3189,plain,(
% 8.75/1.56    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | ~r2_hidden(sK1,sK2)),
% 8.75/1.56    inference(forward_demodulation,[],[f3114,f145])).
% 8.75/1.56  fof(f3114,plain,(
% 8.75/1.56    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | ~r2_hidden(sK1,sK2)),
% 8.75/1.56    inference(superposition,[],[f867,f383])).
% 8.75/1.56  fof(f383,plain,(
% 8.75/1.56    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK1,sK2)),
% 8.75/1.56    inference(forward_demodulation,[],[f380,f37])).
% 8.75/1.56  fof(f380,plain,(
% 8.75/1.56    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)) | ~r2_hidden(sK1,sK2)),
% 8.75/1.56    inference(backward_demodulation,[],[f85,f379])).
% 8.75/1.56  fof(f85,plain,(
% 8.75/1.56    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r2_hidden(sK1,sK2)),
% 8.75/1.56    inference(backward_demodulation,[],[f70,f36])).
% 8.75/1.56  fof(f70,plain,(
% 8.75/1.56    ~r2_hidden(sK1,sK2) | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))),
% 8.75/1.56    inference(definition_unfolding,[],[f32,f69,f39,f69])).
% 8.75/1.56  fof(f32,plain,(
% 8.75/1.56    ~r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 8.75/1.56    inference(cnf_transformation,[],[f24])).
% 8.75/1.56  % SZS output end Proof for theBenchmark
% 8.75/1.56  % (14718)------------------------------
% 8.75/1.56  % (14718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.75/1.56  % (14718)Termination reason: Refutation
% 8.75/1.56  
% 8.75/1.56  % (14718)Memory used [KB]: 17654
% 8.75/1.56  % (14718)Time elapsed: 1.127 s
% 8.75/1.56  % (14718)------------------------------
% 8.75/1.56  % (14718)------------------------------
% 8.75/1.57  % (14693)Success in time 1.185 s
%------------------------------------------------------------------------------
