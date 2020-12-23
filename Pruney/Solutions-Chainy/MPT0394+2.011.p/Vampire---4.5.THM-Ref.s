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
% DateTime   : Thu Dec  3 12:45:57 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 374 expanded)
%              Number of leaves         :   18 ( 106 expanded)
%              Depth                    :   19
%              Number of atoms          :  258 (1385 expanded)
%              Number of equality atoms :  162 ( 740 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f285,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f276,f66,f276,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))
      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1)
      | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) ) ),
    inference(forward_demodulation,[],[f127,f68])).

fof(f68,plain,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f37,f64])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f127,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k4_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),k4_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X1))
      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1)
      | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) ) ),
    inference(forward_demodulation,[],[f126,f68])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),k4_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))
      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1)
      | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) ) ),
    inference(superposition,[],[f71,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) ),
    inference(definition_unfolding,[],[f43,f63,f65,f64,f64])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f63])).

fof(f41,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f52,f65,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f66,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f35,f42,f63])).

fof(f35,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f23])).

fof(f23,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f276,plain,(
    ! [X6,X4,X5] : k1_xboole_0 != k2_enumset1(X4,X4,X5,X6) ),
    inference(subsumption_resolution,[],[f270,f88])).

fof(f88,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f56,f53])).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f270,plain,(
    ! [X6,X4,X5] :
      ( k1_xboole_0 != k2_enumset1(X4,X4,X5,X6)
      | ~ r2_hidden(X4,k2_enumset1(X4,X4,X5,X6)) ) ),
    inference(superposition,[],[f119,f265])).

fof(f265,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f67,f262])).

fof(f262,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(resolution,[],[f242,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f242,plain,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[],[f229,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
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

fof(f229,plain,(
    ! [X5] : ~ r2_hidden(X5,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f224])).

fof(f224,plain,(
    ! [X5] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X5,k1_xboole_0) ) ),
    inference(superposition,[],[f119,f204])).

fof(f204,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f203])).

fof(f203,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f201,f105])).

fof(f105,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f97,f90])).

fof(f90,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(X0,k1_xboole_0),X0) ),
    inference(superposition,[],[f69,f67])).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f97,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,k1_xboole_0)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f49,f91])).

fof(f91,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f69,f67])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f201,plain,(
    ! [X12,X13] :
      ( k4_xboole_0(X12,X12) != X12
      | k4_xboole_0(X12,X13) = X12 ) ),
    inference(subsumption_resolution,[],[f199,f50])).

fof(f199,plain,(
    ! [X12,X13] :
      ( k4_xboole_0(X12,X12) != X12
      | k4_xboole_0(X12,X13) = X12
      | r1_xboole_0(X12,X13) ) ),
    inference(resolution,[],[f130,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f130,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK2(X5,X6),X4)
      | k4_xboole_0(X4,X5) != X4
      | k4_xboole_0(X5,X6) = X5 ) ),
    inference(resolution,[],[f120,f50])).

fof(f120,plain,(
    ! [X14,X12,X13] :
      ( r1_xboole_0(X12,X13)
      | k4_xboole_0(X14,X12) != X14
      | ~ r2_hidden(sK2(X12,X13),X14) ) ),
    inference(resolution,[],[f93,f44])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2)
      | k4_xboole_0(X2,X1) != X2 ) ),
    inference(resolution,[],[f46,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f119,plain,(
    ! [X10,X8,X11,X9] :
      ( k4_xboole_0(X9,k2_enumset1(X8,X8,X10,X11)) != X9
      | ~ r2_hidden(X8,X9) ) ),
    inference(resolution,[],[f93,f88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (26272)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.49  % (26263)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (26255)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (26280)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (26254)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (26280)Refutation not found, incomplete strategy% (26280)------------------------------
% 0.20/0.51  % (26280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26280)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (26280)Memory used [KB]: 1663
% 0.20/0.51  % (26280)Time elapsed: 0.002 s
% 0.20/0.51  % (26280)------------------------------
% 0.20/0.51  % (26280)------------------------------
% 0.20/0.51  % (26250)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (26273)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (26261)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (26266)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.52  % (26261)Refutation not found, incomplete strategy% (26261)------------------------------
% 0.20/0.52  % (26261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26261)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26261)Memory used [KB]: 6268
% 0.20/0.52  % (26261)Time elapsed: 0.124 s
% 0.20/0.52  % (26261)------------------------------
% 0.20/0.52  % (26261)------------------------------
% 0.20/0.52  % (26279)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.52  % (26251)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (26251)Refutation not found, incomplete strategy% (26251)------------------------------
% 0.20/0.52  % (26251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26251)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26251)Memory used [KB]: 1663
% 0.20/0.52  % (26251)Time elapsed: 0.124 s
% 0.20/0.52  % (26251)------------------------------
% 0.20/0.52  % (26251)------------------------------
% 0.20/0.53  % (26275)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (26276)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (26262)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (26276)Refutation not found, incomplete strategy% (26276)------------------------------
% 0.20/0.53  % (26276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26276)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26276)Memory used [KB]: 6140
% 0.20/0.53  % (26276)Time elapsed: 0.129 s
% 0.20/0.53  % (26276)------------------------------
% 0.20/0.53  % (26276)------------------------------
% 0.20/0.53  % (26275)Refutation not found, incomplete strategy% (26275)------------------------------
% 0.20/0.53  % (26275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26275)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26275)Memory used [KB]: 10618
% 0.20/0.53  % (26275)Time elapsed: 0.127 s
% 0.20/0.53  % (26275)------------------------------
% 0.20/0.53  % (26275)------------------------------
% 0.20/0.53  % (26262)Refutation not found, incomplete strategy% (26262)------------------------------
% 0.20/0.53  % (26262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26262)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26262)Memory used [KB]: 10618
% 0.20/0.53  % (26262)Time elapsed: 0.133 s
% 0.20/0.53  % (26262)------------------------------
% 0.20/0.53  % (26262)------------------------------
% 0.20/0.53  % (26253)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (26279)Refutation not found, incomplete strategy% (26279)------------------------------
% 0.20/0.53  % (26279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26271)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (26252)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (26279)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  % (26265)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  
% 0.20/0.53  % (26279)Memory used [KB]: 10746
% 0.20/0.53  % (26279)Time elapsed: 0.132 s
% 0.20/0.53  % (26279)------------------------------
% 0.20/0.53  % (26279)------------------------------
% 0.20/0.53  % (26277)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (26277)Refutation not found, incomplete strategy% (26277)------------------------------
% 0.20/0.53  % (26277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26277)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26277)Memory used [KB]: 6140
% 0.20/0.53  % (26277)Time elapsed: 0.128 s
% 0.20/0.53  % (26277)------------------------------
% 0.20/0.53  % (26277)------------------------------
% 0.20/0.53  % (26264)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (26264)Refutation not found, incomplete strategy% (26264)------------------------------
% 0.20/0.53  % (26264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26264)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26264)Memory used [KB]: 1663
% 0.20/0.53  % (26264)Time elapsed: 0.089 s
% 0.20/0.53  % (26264)------------------------------
% 0.20/0.53  % (26264)------------------------------
% 0.20/0.53  % (26278)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (26267)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (26278)Refutation not found, incomplete strategy% (26278)------------------------------
% 0.20/0.53  % (26278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26278)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26278)Memory used [KB]: 6140
% 0.20/0.53  % (26278)Time elapsed: 0.139 s
% 0.20/0.53  % (26278)------------------------------
% 0.20/0.53  % (26278)------------------------------
% 0.20/0.53  % (26267)Refutation not found, incomplete strategy% (26267)------------------------------
% 0.20/0.53  % (26267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26267)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26267)Memory used [KB]: 1663
% 0.20/0.53  % (26267)Time elapsed: 0.139 s
% 0.20/0.53  % (26267)------------------------------
% 0.20/0.53  % (26267)------------------------------
% 0.20/0.54  % (26258)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (26259)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (26269)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (26256)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (26266)Refutation not found, incomplete strategy% (26266)------------------------------
% 0.20/0.54  % (26266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (26266)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (26266)Memory used [KB]: 10618
% 0.20/0.54  % (26266)Time elapsed: 0.139 s
% 0.20/0.54  % (26266)------------------------------
% 0.20/0.54  % (26266)------------------------------
% 0.20/0.54  % (26260)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (26268)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (26268)Refutation not found, incomplete strategy% (26268)------------------------------
% 0.20/0.54  % (26268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (26274)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.55  % (26268)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (26268)Memory used [KB]: 1663
% 0.20/0.55  % (26268)Time elapsed: 0.149 s
% 0.20/0.55  % (26268)------------------------------
% 0.20/0.55  % (26268)------------------------------
% 1.56/0.55  % (26257)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.56/0.55  % (26273)Refutation found. Thanks to Tanya!
% 1.56/0.55  % SZS status Theorem for theBenchmark
% 1.56/0.55  % SZS output start Proof for theBenchmark
% 1.56/0.55  fof(f285,plain,(
% 1.56/0.55    $false),
% 1.56/0.55    inference(unit_resulting_resolution,[],[f276,f66,f276,f128])).
% 1.56/0.55  fof(f128,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0)) )),
% 1.56/0.55    inference(forward_demodulation,[],[f127,f68])).
% 1.56/0.55  fof(f68,plain,(
% 1.56/0.55    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 1.56/0.55    inference(definition_unfolding,[],[f37,f64])).
% 1.56/0.55  fof(f64,plain,(
% 1.56/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.56/0.55    inference(definition_unfolding,[],[f38,f63])).
% 1.56/0.55  fof(f63,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.56/0.55    inference(definition_unfolding,[],[f40,f53])).
% 1.56/0.55  fof(f53,plain,(
% 1.56/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f12])).
% 1.56/0.55  fof(f12,axiom,(
% 1.56/0.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.56/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.56/0.55  fof(f40,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f11])).
% 1.56/0.55  fof(f11,axiom,(
% 1.56/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.56/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.56/0.55  fof(f38,plain,(
% 1.56/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f10])).
% 1.56/0.55  fof(f10,axiom,(
% 1.56/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.56/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.56/0.55  fof(f37,plain,(
% 1.56/0.55    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 1.56/0.55    inference(cnf_transformation,[],[f15])).
% 1.56/0.55  fof(f15,axiom,(
% 1.56/0.55    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.56/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.56/0.55  fof(f127,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k4_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),k4_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X1)) | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0)) )),
% 1.56/0.55    inference(forward_demodulation,[],[f126,f68])).
% 1.56/0.55  fof(f126,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k4_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),k4_xboole_0(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0)) )),
% 1.56/0.55    inference(superposition,[],[f71,f70])).
% 1.56/0.55  fof(f70,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))) )),
% 1.56/0.55    inference(definition_unfolding,[],[f43,f63,f65,f64,f64])).
% 1.56/0.55  fof(f65,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.56/0.55    inference(definition_unfolding,[],[f41,f63])).
% 1.56/0.55  fof(f41,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f13])).
% 1.56/0.55  fof(f13,axiom,(
% 1.56/0.55    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.56/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.56/0.55  fof(f43,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.56/0.55    inference(cnf_transformation,[],[f8])).
% 1.56/0.55  fof(f8,axiom,(
% 1.56/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.56/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 1.56/0.55  fof(f71,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.56/0.55    inference(definition_unfolding,[],[f52,f65,f42])).
% 1.56/0.55  fof(f42,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.56/0.55    inference(cnf_transformation,[],[f5])).
% 1.56/0.55  fof(f5,axiom,(
% 1.56/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.56/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.56/0.55  fof(f52,plain,(
% 1.56/0.55    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.56/0.55    inference(cnf_transformation,[],[f21])).
% 1.56/0.55  fof(f21,plain,(
% 1.56/0.55    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.56/0.55    inference(ennf_transformation,[],[f14])).
% 1.56/0.55  fof(f14,axiom,(
% 1.56/0.55    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.56/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).
% 1.56/0.55  fof(f66,plain,(
% 1.56/0.55    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),
% 1.56/0.55    inference(definition_unfolding,[],[f35,f42,f63])).
% 1.56/0.55  fof(f35,plain,(
% 1.56/0.55    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.56/0.55    inference(cnf_transformation,[],[f24])).
% 1.56/0.55  fof(f24,plain,(
% 1.56/0.55    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.56/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f23])).
% 1.56/0.55  fof(f23,plain,(
% 1.56/0.55    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.56/0.55    introduced(choice_axiom,[])).
% 1.56/0.55  fof(f19,plain,(
% 1.56/0.55    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 1.56/0.55    inference(ennf_transformation,[],[f17])).
% 1.56/0.55  fof(f17,negated_conjecture,(
% 1.56/0.55    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.56/0.55    inference(negated_conjecture,[],[f16])).
% 1.56/0.55  fof(f16,conjecture,(
% 1.56/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.56/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.56/0.55  fof(f276,plain,(
% 1.56/0.55    ( ! [X6,X4,X5] : (k1_xboole_0 != k2_enumset1(X4,X4,X5,X6)) )),
% 1.56/0.55    inference(subsumption_resolution,[],[f270,f88])).
% 1.56/0.55  fof(f88,plain,(
% 1.56/0.55    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 1.56/0.55    inference(equality_resolution,[],[f87])).
% 1.56/0.55  fof(f87,plain,(
% 1.56/0.55    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 1.56/0.55    inference(equality_resolution,[],[f79])).
% 1.56/0.55  fof(f79,plain,(
% 1.56/0.55    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.56/0.55    inference(definition_unfolding,[],[f56,f53])).
% 1.56/0.55  fof(f56,plain,(
% 1.56/0.55    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.56/0.55    inference(cnf_transformation,[],[f34])).
% 1.56/0.55  fof(f34,plain,(
% 1.56/0.55    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.56/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 1.56/0.55  fof(f33,plain,(
% 1.56/0.55    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 1.56/0.55    introduced(choice_axiom,[])).
% 1.56/0.55  fof(f32,plain,(
% 1.56/0.55    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.56/0.55    inference(rectify,[],[f31])).
% 1.56/0.55  fof(f31,plain,(
% 1.56/0.55    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.56/0.55    inference(flattening,[],[f30])).
% 1.56/0.55  fof(f30,plain,(
% 1.56/0.55    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.56/0.55    inference(nnf_transformation,[],[f22])).
% 1.56/0.55  fof(f22,plain,(
% 1.56/0.55    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.56/0.55    inference(ennf_transformation,[],[f7])).
% 1.56/0.55  fof(f7,axiom,(
% 1.56/0.55    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.56/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.56/0.55  fof(f270,plain,(
% 1.56/0.55    ( ! [X6,X4,X5] : (k1_xboole_0 != k2_enumset1(X4,X4,X5,X6) | ~r2_hidden(X4,k2_enumset1(X4,X4,X5,X6))) )),
% 1.56/0.55    inference(superposition,[],[f119,f265])).
% 1.56/0.55  fof(f265,plain,(
% 1.56/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.56/0.55    inference(backward_demodulation,[],[f67,f262])).
% 1.56/0.55  fof(f262,plain,(
% 1.56/0.55    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.56/0.55    inference(resolution,[],[f242,f50])).
% 1.56/0.55  fof(f50,plain,(
% 1.56/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.56/0.55    inference(cnf_transformation,[],[f29])).
% 1.56/0.55  fof(f29,plain,(
% 1.56/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.56/0.55    inference(nnf_transformation,[],[f6])).
% 1.56/0.55  fof(f6,axiom,(
% 1.56/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.56/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.56/0.55  fof(f242,plain,(
% 1.56/0.55    ( ! [X1] : (r1_xboole_0(X1,k1_xboole_0)) )),
% 1.56/0.55    inference(resolution,[],[f229,f45])).
% 1.56/0.55  fof(f45,plain,(
% 1.56/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.56/0.55    inference(cnf_transformation,[],[f26])).
% 1.56/0.55  fof(f26,plain,(
% 1.56/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.56/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f25])).
% 1.56/0.55  fof(f25,plain,(
% 1.56/0.55    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.56/0.55    introduced(choice_axiom,[])).
% 1.56/0.55  fof(f20,plain,(
% 1.56/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.56/0.55    inference(ennf_transformation,[],[f18])).
% 1.56/0.55  fof(f18,plain,(
% 1.56/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.56/0.55    inference(rectify,[],[f1])).
% 1.56/0.55  fof(f1,axiom,(
% 1.56/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.56/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.56/0.55  fof(f229,plain,(
% 1.56/0.55    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0)) )),
% 1.56/0.55    inference(trivial_inequality_removal,[],[f224])).
% 1.56/0.55  fof(f224,plain,(
% 1.56/0.55    ( ! [X5] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X5,k1_xboole_0)) )),
% 1.56/0.55    inference(superposition,[],[f119,f204])).
% 1.56/0.55  fof(f204,plain,(
% 1.56/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.56/0.55    inference(trivial_inequality_removal,[],[f203])).
% 1.56/0.55  fof(f203,plain,(
% 1.56/0.55    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.56/0.55    inference(superposition,[],[f201,f105])).
% 1.56/0.55  fof(f105,plain,(
% 1.56/0.55    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.56/0.55    inference(resolution,[],[f97,f90])).
% 1.56/0.55  fof(f90,plain,(
% 1.56/0.55    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,k1_xboole_0),X0)) )),
% 1.56/0.55    inference(superposition,[],[f69,f67])).
% 1.56/0.56  fof(f69,plain,(
% 1.56/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.56/0.56    inference(definition_unfolding,[],[f39,f42])).
% 1.56/0.56  fof(f39,plain,(
% 1.56/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f3])).
% 1.56/0.56  fof(f3,axiom,(
% 1.56/0.56    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.56/0.56  fof(f97,plain,(
% 1.56/0.56    ( ! [X4] : (~r1_tarski(X4,k1_xboole_0) | k1_xboole_0 = X4) )),
% 1.56/0.56    inference(resolution,[],[f49,f91])).
% 1.56/0.56  fof(f91,plain,(
% 1.56/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.56/0.56    inference(superposition,[],[f69,f67])).
% 1.56/0.56  fof(f49,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f28])).
% 1.56/0.56  fof(f28,plain,(
% 1.56/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.56    inference(flattening,[],[f27])).
% 1.56/0.56  fof(f27,plain,(
% 1.56/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.56    inference(nnf_transformation,[],[f2])).
% 1.56/0.56  fof(f2,axiom,(
% 1.56/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.56/0.56  fof(f201,plain,(
% 1.56/0.56    ( ! [X12,X13] : (k4_xboole_0(X12,X12) != X12 | k4_xboole_0(X12,X13) = X12) )),
% 1.56/0.56    inference(subsumption_resolution,[],[f199,f50])).
% 1.56/0.56  fof(f199,plain,(
% 1.56/0.56    ( ! [X12,X13] : (k4_xboole_0(X12,X12) != X12 | k4_xboole_0(X12,X13) = X12 | r1_xboole_0(X12,X13)) )),
% 1.56/0.56    inference(resolution,[],[f130,f44])).
% 1.56/0.56  fof(f44,plain,(
% 1.56/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f26])).
% 1.56/0.56  fof(f130,plain,(
% 1.56/0.56    ( ! [X6,X4,X5] : (~r2_hidden(sK2(X5,X6),X4) | k4_xboole_0(X4,X5) != X4 | k4_xboole_0(X5,X6) = X5) )),
% 1.56/0.56    inference(resolution,[],[f120,f50])).
% 1.56/0.56  fof(f120,plain,(
% 1.56/0.56    ( ! [X14,X12,X13] : (r1_xboole_0(X12,X13) | k4_xboole_0(X14,X12) != X14 | ~r2_hidden(sK2(X12,X13),X14)) )),
% 1.56/0.56    inference(resolution,[],[f93,f44])).
% 1.56/0.56  fof(f93,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,X2) | k4_xboole_0(X2,X1) != X2) )),
% 1.56/0.56    inference(resolution,[],[f46,f51])).
% 1.56/0.56  fof(f51,plain,(
% 1.56/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 1.56/0.56    inference(cnf_transformation,[],[f29])).
% 1.56/0.56  fof(f46,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f26])).
% 1.56/0.56  fof(f67,plain,(
% 1.56/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.56/0.56    inference(definition_unfolding,[],[f36,f42])).
% 1.56/0.56  fof(f36,plain,(
% 1.56/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f4])).
% 1.56/0.56  fof(f4,axiom,(
% 1.56/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.56/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.56/0.56  fof(f119,plain,(
% 1.56/0.56    ( ! [X10,X8,X11,X9] : (k4_xboole_0(X9,k2_enumset1(X8,X8,X10,X11)) != X9 | ~r2_hidden(X8,X9)) )),
% 1.56/0.56    inference(resolution,[],[f93,f88])).
% 1.56/0.56  % SZS output end Proof for theBenchmark
% 1.56/0.56  % (26273)------------------------------
% 1.56/0.56  % (26273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.56  % (26273)Termination reason: Refutation
% 1.56/0.56  
% 1.56/0.56  % (26273)Memory used [KB]: 6524
% 1.56/0.56  % (26273)Time elapsed: 0.117 s
% 1.56/0.56  % (26273)------------------------------
% 1.56/0.56  % (26273)------------------------------
% 1.56/0.57  % (26249)Success in time 0.205 s
%------------------------------------------------------------------------------
