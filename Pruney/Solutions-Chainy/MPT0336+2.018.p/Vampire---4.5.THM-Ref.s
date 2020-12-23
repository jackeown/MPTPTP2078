%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 139 expanded)
%              Number of leaves         :   18 (  39 expanded)
%              Depth                    :   17
%              Number of atoms          :  181 ( 355 expanded)
%              Number of equality atoms :   30 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1682,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1674,f38])).

fof(f38,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f1674,plain,(
    r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[],[f1632,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1632,plain,(
    r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f1595,f456])).

fof(f456,plain,(
    ! [X12] :
      ( ~ r1_xboole_0(sK1,X12)
      | r1_xboole_0(sK1,k2_xboole_0(X12,sK2)) ) ),
    inference(resolution,[],[f56,f65])).

fof(f65,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f51,f37])).

fof(f37,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f1595,plain,(
    r1_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1580,f36])).

fof(f36,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f1580,plain,
    ( ~ r2_hidden(sK3,sK2)
    | r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f293,f1132])).

fof(f1132,plain,
    ( r2_hidden(sK3,k3_xboole_0(sK0,sK1))
    | r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f64,f203])).

fof(f203,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1))
    | r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f194,f123])).

fof(f123,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,k3_xboole_0(sK0,sK1))
      | ~ r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1)) ) ),
    inference(superposition,[],[f69,f73])).

fof(f73,plain,(
    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(resolution,[],[f50,f63])).

fof(f63,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f35,f62])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X1,X0))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f45,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f194,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X1,X0))
      | r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f44,f42])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f62])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f293,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X1,sK1))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f267,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
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

fof(f267,plain,(
    ! [X0] : r1_xboole_0(k3_xboole_0(X0,sK1),sK2) ),
    inference(superposition,[],[f254,f42])).

fof(f254,plain,(
    ! [X10] : r1_xboole_0(k3_xboole_0(sK1,X10),sK2) ),
    inference(trivial_inequality_removal,[],[f252])).

fof(f252,plain,(
    ! [X10] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k3_xboole_0(sK1,X10),sK2) ) ),
    inference(superposition,[],[f100,f240])).

fof(f240,plain,(
    ! [X16] : k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(sK1,X16)) ),
    inference(forward_demodulation,[],[f219,f78])).

fof(f78,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(resolution,[],[f52,f66])).

fof(f66,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f51,f39])).

fof(f39,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f219,plain,(
    ! [X16] : k3_xboole_0(sK2,k3_xboole_0(sK1,X16)) = k3_xboole_0(k1_xboole_0,X16) ),
    inference(superposition,[],[f55,f80])).

fof(f80,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f52,f37])).

fof(f55,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f100,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,X0) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f53,f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:08:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (20003)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.45  % (20005)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (19995)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (19991)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (19992)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (20007)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.47  % (20004)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (20002)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (20001)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (19999)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (19998)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (19994)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (19990)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (20008)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (19997)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (19993)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (19996)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (20006)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.52  % (20004)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f1682,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f1674,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 0.21/0.52    inference(ennf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.21/0.52    inference(negated_conjecture,[],[f16])).
% 0.21/0.52  fof(f16,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 0.21/0.52  fof(f1674,plain,(
% 0.21/0.52    r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.21/0.52    inference(resolution,[],[f1632,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.52  fof(f1632,plain,(
% 0.21/0.52    r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 0.21/0.52    inference(resolution,[],[f1595,f456])).
% 0.21/0.52  fof(f456,plain,(
% 0.21/0.52    ( ! [X12] : (~r1_xboole_0(sK1,X12) | r1_xboole_0(sK1,k2_xboole_0(X12,sK2))) )),
% 0.21/0.52    inference(resolution,[],[f56,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    r1_xboole_0(sK1,sK2)),
% 0.21/0.52    inference(resolution,[],[f51,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    r1_xboole_0(sK2,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.21/0.52  fof(f1595,plain,(
% 0.21/0.52    r1_xboole_0(sK1,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f1580,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    r2_hidden(sK3,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f1580,plain,(
% 0.21/0.52    ~r2_hidden(sK3,sK2) | r1_xboole_0(sK1,sK0)),
% 0.21/0.52    inference(resolution,[],[f293,f1132])).
% 0.21/0.52  fof(f1132,plain,(
% 0.21/0.52    r2_hidden(sK3,k3_xboole_0(sK0,sK1)) | r1_xboole_0(sK1,sK0)),
% 0.21/0.52    inference(resolution,[],[f64,f203])).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    ~r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1)) | r1_xboole_0(sK1,sK0)),
% 0.21/0.52    inference(resolution,[],[f194,f123])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    ( ! [X8] : (~r2_hidden(X8,k3_xboole_0(sK0,sK1)) | ~r1_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(sK0,sK1))) )),
% 0.21/0.52    inference(superposition,[],[f69,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),
% 0.21/0.52    inference(resolution,[],[f50,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    r1_tarski(k3_xboole_0(sK0,sK1),k3_enumset1(sK3,sK3,sK3,sK3,sK3))),
% 0.21/0.52    inference(definition_unfolding,[],[f35,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f40,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f43,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f54,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(superposition,[],[f45,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X1,X0)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(superposition,[],[f44,f42])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f49,f62])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.52  fof(f293,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,sK1)) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.52    inference(resolution,[],[f267,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.52  fof(f267,plain,(
% 0.21/0.52    ( ! [X0] : (r1_xboole_0(k3_xboole_0(X0,sK1),sK2)) )),
% 0.21/0.52    inference(superposition,[],[f254,f42])).
% 0.21/0.52  fof(f254,plain,(
% 0.21/0.52    ( ! [X10] : (r1_xboole_0(k3_xboole_0(sK1,X10),sK2)) )),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f252])).
% 0.21/0.52  fof(f252,plain,(
% 0.21/0.52    ( ! [X10] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k3_xboole_0(sK1,X10),sK2)) )),
% 0.21/0.52    inference(superposition,[],[f100,f240])).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    ( ! [X16] : (k1_xboole_0 = k3_xboole_0(sK2,k3_xboole_0(sK1,X16))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f219,f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f52,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(resolution,[],[f51,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.52  fof(f219,plain,(
% 0.21/0.52    ( ! [X16] : (k3_xboole_0(sK2,k3_xboole_0(sK1,X16)) = k3_xboole_0(k1_xboole_0,X16)) )),
% 0.21/0.52    inference(superposition,[],[f55,f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 0.21/0.52    inference(resolution,[],[f52,f37])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X1,X0) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(superposition,[],[f53,f42])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (20004)------------------------------
% 0.21/0.52  % (20004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20004)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (20004)Memory used [KB]: 2302
% 0.21/0.52  % (20004)Time elapsed: 0.082 s
% 0.21/0.52  % (20004)------------------------------
% 0.21/0.52  % (20004)------------------------------
% 0.21/0.52  % (19986)Success in time 0.164 s
%------------------------------------------------------------------------------
