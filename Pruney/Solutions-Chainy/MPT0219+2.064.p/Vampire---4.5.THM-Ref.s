%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 234 expanded)
%              Number of leaves         :   16 (  78 expanded)
%              Depth                    :   23
%              Number of atoms          :  220 ( 385 expanded)
%              Number of equality atoms :  170 ( 335 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f533,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f532])).

fof(f532,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f32,f506])).

fof(f506,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f501,f77])).

fof(f77,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f37,f41])).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f501,plain,(
    r2_hidden(sK1,k2_tarski(sK0,sK0)) ),
    inference(forward_demodulation,[],[f500,f46])).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f500,plain,(
    r2_hidden(sK1,k5_xboole_0(k2_tarski(sK0,sK0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f489,f122])).

fof(f122,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f62,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f35,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f34,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f36,f45,f56])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f489,plain,(
    r2_hidden(sK1,k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)))) ),
    inference(superposition,[],[f81,f478])).

fof(f478,plain,(
    k2_tarski(sK1,sK1) = k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK0,sK0)) ),
    inference(forward_demodulation,[],[f477,f46])).

fof(f477,plain,(
    k2_tarski(sK1,sK1) = k3_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK0,sK0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f476,f122])).

fof(f476,plain,(
    k2_tarski(sK1,sK1) = k3_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)))) ),
    inference(forward_demodulation,[],[f475,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f475,plain,(
    k2_tarski(sK1,sK1) = k3_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))) ),
    inference(forward_demodulation,[],[f474,f375])).

fof(f375,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f125,f345])).

fof(f345,plain,(
    ! [X8] : k5_xboole_0(k1_xboole_0,X8) = X8 ),
    inference(forward_demodulation,[],[f307,f46])).

fof(f307,plain,(
    ! [X8] : k5_xboole_0(k1_xboole_0,X8) = k5_xboole_0(X8,k1_xboole_0) ),
    inference(superposition,[],[f125,f122])).

fof(f125,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f44,f122])).

fof(f474,plain,(
    k2_tarski(sK1,sK1) = k3_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))))) ),
    inference(forward_demodulation,[],[f459,f44])).

fof(f459,plain,(
    k2_tarski(sK1,sK1) = k3_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))),k2_tarski(sK1,sK1)))) ),
    inference(superposition,[],[f99,f130])).

fof(f130,plain,(
    k2_tarski(sK1,sK1) = k3_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)))) ),
    inference(superposition,[],[f61,f129])).

fof(f129,plain,(
    k5_xboole_0(k2_tarski(sK0,sK0),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))) = k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) ),
    inference(forward_demodulation,[],[f127,f46])).

fof(f127,plain,(
    k5_xboole_0(k2_tarski(sK0,sK0),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))) = k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK1),k1_xboole_0)) ),
    inference(superposition,[],[f96,f122])).

fof(f96,plain,(
    ! [X2] : k5_xboole_0(k2_tarski(sK0,sK0),X2) = k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)),X2))) ),
    inference(forward_demodulation,[],[f92,f44])).

fof(f92,plain,(
    ! [X2] : k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))),X2)) = k5_xboole_0(k2_tarski(sK0,sK0),X2) ),
    inference(superposition,[],[f44,f89])).

fof(f89,plain,(
    k2_tarski(sK0,sK0) = k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)))) ),
    inference(backward_demodulation,[],[f60,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f60,plain,(
    k2_tarski(sK0,sK0) = k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK0,sK0)))) ),
    inference(definition_unfolding,[],[f31,f41,f56,f41,f41])).

fof(f31,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f99,plain,(
    ! [X0,X1] : k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X1 ),
    inference(superposition,[],[f61,f47])).

fof(f81,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X5,X2),k3_xboole_0(k2_tarski(X5,X2),k2_tarski(X0,X0))))) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X5,X2),k3_xboole_0(k2_tarski(X5,X2),k2_tarski(X0,X0)))) != X3 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3 ) ),
    inference(definition_unfolding,[],[f50,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) ),
    inference(definition_unfolding,[],[f43,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f33,f56])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
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

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f32,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n010.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 11:13:44 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.53  % (750)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (745)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (767)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (775)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (771)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (748)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (748)Refutation not found, incomplete strategy% (748)------------------------------
% 0.21/0.54  % (748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (748)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (748)Memory used [KB]: 1663
% 0.21/0.55  % (748)Time elapsed: 0.125 s
% 0.21/0.55  % (748)------------------------------
% 0.21/0.55  % (748)------------------------------
% 0.21/0.55  % (751)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (752)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (766)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (761)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (758)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (774)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (763)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (754)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (763)Refutation not found, incomplete strategy% (763)------------------------------
% 0.21/0.55  % (763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (763)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (763)Memory used [KB]: 10618
% 0.21/0.55  % (763)Time elapsed: 0.138 s
% 0.21/0.55  % (763)------------------------------
% 0.21/0.55  % (763)------------------------------
% 0.21/0.55  % (781)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (780)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (753)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (762)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (781)Refutation not found, incomplete strategy% (781)------------------------------
% 0.21/0.55  % (781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (781)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (781)Memory used [KB]: 1663
% 0.21/0.55  % (781)Time elapsed: 0.002 s
% 0.21/0.55  % (781)------------------------------
% 0.21/0.55  % (781)------------------------------
% 0.21/0.56  % (749)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.56  % (764)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (769)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  % (779)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (768)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (772)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (755)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (760)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (757)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (756)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.57  % (759)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.57  % (759)Refutation not found, incomplete strategy% (759)------------------------------
% 0.21/0.57  % (759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (759)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (759)Memory used [KB]: 10618
% 0.21/0.57  % (759)Time elapsed: 0.150 s
% 0.21/0.57  % (759)------------------------------
% 0.21/0.57  % (759)------------------------------
% 0.21/0.57  % (778)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.58  % (752)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 1.43/0.58  % SZS output start Proof for theBenchmark
% 1.43/0.58  fof(f533,plain,(
% 1.43/0.58    $false),
% 1.43/0.58    inference(trivial_inequality_removal,[],[f532])).
% 1.43/0.58  fof(f532,plain,(
% 1.43/0.58    sK0 != sK0),
% 1.43/0.58    inference(superposition,[],[f32,f506])).
% 1.43/0.58  fof(f506,plain,(
% 1.43/0.58    sK0 = sK1),
% 1.43/0.58    inference(resolution,[],[f501,f77])).
% 1.43/0.58  fof(f77,plain,(
% 1.43/0.58    ( ! [X0,X3] : (~r2_hidden(X3,k2_tarski(X0,X0)) | X0 = X3) )),
% 1.43/0.58    inference(equality_resolution,[],[f66])).
% 1.43/0.58  fof(f66,plain,(
% 1.43/0.58    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 1.43/0.58    inference(definition_unfolding,[],[f37,f41])).
% 1.43/0.58  fof(f41,plain,(
% 1.43/0.58    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f12])).
% 1.43/0.58  fof(f12,axiom,(
% 1.43/0.58    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.43/0.58  fof(f37,plain,(
% 1.43/0.58    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.43/0.58    inference(cnf_transformation,[],[f25])).
% 1.43/0.58  fof(f25,plain,(
% 1.43/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.43/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).
% 1.43/0.58  fof(f24,plain,(
% 1.43/0.58    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.43/0.58    introduced(choice_axiom,[])).
% 1.43/0.58  fof(f23,plain,(
% 1.43/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.43/0.58    inference(rectify,[],[f22])).
% 1.43/0.58  fof(f22,plain,(
% 1.43/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.43/0.58    inference(nnf_transformation,[],[f9])).
% 1.43/0.58  fof(f9,axiom,(
% 1.43/0.58    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.43/0.58  fof(f501,plain,(
% 1.43/0.58    r2_hidden(sK1,k2_tarski(sK0,sK0))),
% 1.43/0.58    inference(forward_demodulation,[],[f500,f46])).
% 1.43/0.58  fof(f46,plain,(
% 1.43/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.43/0.58    inference(cnf_transformation,[],[f5])).
% 1.43/0.58  fof(f5,axiom,(
% 1.43/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.43/0.58  fof(f500,plain,(
% 1.43/0.58    r2_hidden(sK1,k5_xboole_0(k2_tarski(sK0,sK0),k1_xboole_0))),
% 1.43/0.58    inference(forward_demodulation,[],[f489,f122])).
% 1.43/0.58  fof(f122,plain,(
% 1.43/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.43/0.58    inference(forward_demodulation,[],[f62,f61])).
% 1.43/0.58  fof(f61,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 1.43/0.58    inference(definition_unfolding,[],[f35,f56])).
% 1.43/0.58  fof(f56,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.43/0.58    inference(definition_unfolding,[],[f34,f45])).
% 1.43/0.58  fof(f45,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.43/0.58    inference(cnf_transformation,[],[f2])).
% 1.43/0.58  fof(f2,axiom,(
% 1.43/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.43/0.58  fof(f34,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.43/0.58    inference(cnf_transformation,[],[f7])).
% 1.43/0.58  fof(f7,axiom,(
% 1.43/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.43/0.58  fof(f35,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.43/0.58    inference(cnf_transformation,[],[f3])).
% 1.43/0.58  fof(f3,axiom,(
% 1.43/0.58    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.43/0.58  fof(f62,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 1.43/0.58    inference(definition_unfolding,[],[f36,f45,f56])).
% 1.43/0.58  fof(f36,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 1.43/0.58    inference(cnf_transformation,[],[f4])).
% 1.43/0.58  fof(f4,axiom,(
% 1.43/0.58    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.43/0.58  fof(f489,plain,(
% 1.43/0.58    r2_hidden(sK1,k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1))))),
% 1.43/0.58    inference(superposition,[],[f81,f478])).
% 1.43/0.58  fof(f478,plain,(
% 1.43/0.58    k2_tarski(sK1,sK1) = k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK0,sK0))),
% 1.43/0.58    inference(forward_demodulation,[],[f477,f46])).
% 1.43/0.58  fof(f477,plain,(
% 1.43/0.58    k2_tarski(sK1,sK1) = k3_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK0,sK0),k1_xboole_0))),
% 1.43/0.58    inference(forward_demodulation,[],[f476,f122])).
% 1.43/0.58  fof(f476,plain,(
% 1.43/0.58    k2_tarski(sK1,sK1) = k3_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1))))),
% 1.43/0.58    inference(forward_demodulation,[],[f475,f44])).
% 1.43/0.58  fof(f44,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.43/0.58    inference(cnf_transformation,[],[f6])).
% 1.43/0.58  fof(f6,axiom,(
% 1.43/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.43/0.58  fof(f475,plain,(
% 1.43/0.58    k2_tarski(sK1,sK1) = k3_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)))),
% 1.43/0.58    inference(forward_demodulation,[],[f474,f375])).
% 1.43/0.58  fof(f375,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.43/0.58    inference(backward_demodulation,[],[f125,f345])).
% 1.43/0.58  fof(f345,plain,(
% 1.43/0.58    ( ! [X8] : (k5_xboole_0(k1_xboole_0,X8) = X8) )),
% 1.43/0.58    inference(forward_demodulation,[],[f307,f46])).
% 1.43/0.58  fof(f307,plain,(
% 1.43/0.58    ( ! [X8] : (k5_xboole_0(k1_xboole_0,X8) = k5_xboole_0(X8,k1_xboole_0)) )),
% 1.43/0.58    inference(superposition,[],[f125,f122])).
% 1.43/0.58  fof(f125,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.43/0.58    inference(superposition,[],[f44,f122])).
% 1.43/0.58  fof(f474,plain,(
% 1.43/0.58    k2_tarski(sK1,sK1) = k3_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)))))),
% 1.43/0.58    inference(forward_demodulation,[],[f459,f44])).
% 1.43/0.58  fof(f459,plain,(
% 1.43/0.58    k2_tarski(sK1,sK1) = k3_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))),k2_tarski(sK1,sK1))))),
% 1.43/0.58    inference(superposition,[],[f99,f130])).
% 1.43/0.58  fof(f130,plain,(
% 1.43/0.58    k2_tarski(sK1,sK1) = k3_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))))),
% 1.43/0.58    inference(superposition,[],[f61,f129])).
% 1.43/0.58  fof(f129,plain,(
% 1.43/0.58    k5_xboole_0(k2_tarski(sK0,sK0),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))) = k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))),
% 1.43/0.58    inference(forward_demodulation,[],[f127,f46])).
% 1.43/0.58  fof(f127,plain,(
% 1.43/0.58    k5_xboole_0(k2_tarski(sK0,sK0),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))) = k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK1),k1_xboole_0))),
% 1.43/0.58    inference(superposition,[],[f96,f122])).
% 1.43/0.58  fof(f96,plain,(
% 1.43/0.58    ( ! [X2] : (k5_xboole_0(k2_tarski(sK0,sK0),X2) = k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)),X2)))) )),
% 1.43/0.58    inference(forward_demodulation,[],[f92,f44])).
% 1.43/0.58  fof(f92,plain,(
% 1.43/0.58    ( ! [X2] : (k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))),X2)) = k5_xboole_0(k2_tarski(sK0,sK0),X2)) )),
% 1.43/0.58    inference(superposition,[],[f44,f89])).
% 1.43/0.58  fof(f89,plain,(
% 1.43/0.58    k2_tarski(sK0,sK0) = k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1))))),
% 1.43/0.58    inference(backward_demodulation,[],[f60,f47])).
% 1.43/0.58  fof(f47,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f1])).
% 1.43/0.58  fof(f1,axiom,(
% 1.43/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.43/0.58  fof(f60,plain,(
% 1.43/0.58    k2_tarski(sK0,sK0) = k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK1,sK1),k3_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK0,sK0))))),
% 1.43/0.58    inference(definition_unfolding,[],[f31,f41,f56,f41,f41])).
% 1.43/0.58  fof(f31,plain,(
% 1.43/0.58    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.43/0.58    inference(cnf_transformation,[],[f21])).
% 1.43/0.58  fof(f21,plain,(
% 1.43/0.58    sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.43/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).
% 1.43/0.58  fof(f20,plain,(
% 1.43/0.58    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.43/0.58    introduced(choice_axiom,[])).
% 1.43/0.58  fof(f18,plain,(
% 1.43/0.58    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.43/0.58    inference(ennf_transformation,[],[f17])).
% 1.43/0.58  fof(f17,negated_conjecture,(
% 1.43/0.58    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.43/0.58    inference(negated_conjecture,[],[f16])).
% 1.43/0.58  fof(f16,conjecture,(
% 1.43/0.58    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 1.43/0.58  fof(f99,plain,(
% 1.43/0.58    ( ! [X0,X1] : (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X1) )),
% 1.43/0.58    inference(superposition,[],[f61,f47])).
% 1.43/0.58  fof(f81,plain,(
% 1.43/0.58    ( ! [X2,X0,X5] : (r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X5,X2),k3_xboole_0(k2_tarski(X5,X2),k2_tarski(X0,X0)))))) )),
% 1.43/0.58    inference(equality_resolution,[],[f80])).
% 1.43/0.58  fof(f80,plain,(
% 1.43/0.58    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X5,X2),k3_xboole_0(k2_tarski(X5,X2),k2_tarski(X0,X0)))) != X3) )),
% 1.43/0.58    inference(equality_resolution,[],[f72])).
% 1.43/0.58  fof(f72,plain,(
% 1.43/0.58    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3) )),
% 1.43/0.58    inference(definition_unfolding,[],[f50,f58])).
% 1.43/0.58  fof(f58,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) )),
% 1.43/0.58    inference(definition_unfolding,[],[f43,f57])).
% 1.43/0.58  fof(f57,plain,(
% 1.43/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))))) )),
% 1.43/0.58    inference(definition_unfolding,[],[f33,f56])).
% 1.43/0.58  fof(f33,plain,(
% 1.43/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.43/0.58    inference(cnf_transformation,[],[f10])).
% 1.43/0.58  fof(f10,axiom,(
% 1.43/0.58    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 1.43/0.58  fof(f43,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f14])).
% 1.43/0.58  fof(f14,axiom,(
% 1.43/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.43/0.58  fof(f50,plain,(
% 1.43/0.58    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.43/0.58    inference(cnf_transformation,[],[f30])).
% 1.43/0.58  fof(f30,plain,(
% 1.43/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.43/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 1.43/0.58  fof(f29,plain,(
% 1.43/0.58    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 1.43/0.58    introduced(choice_axiom,[])).
% 1.43/0.59  fof(f28,plain,(
% 1.43/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.43/0.59    inference(rectify,[],[f27])).
% 1.43/0.59  fof(f27,plain,(
% 1.43/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.43/0.59    inference(flattening,[],[f26])).
% 1.43/0.59  fof(f26,plain,(
% 1.43/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.43/0.59    inference(nnf_transformation,[],[f19])).
% 1.43/0.59  fof(f19,plain,(
% 1.43/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.43/0.59    inference(ennf_transformation,[],[f8])).
% 1.43/0.59  fof(f8,axiom,(
% 1.43/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.43/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.43/0.59  fof(f32,plain,(
% 1.43/0.59    sK0 != sK1),
% 1.43/0.59    inference(cnf_transformation,[],[f21])).
% 1.43/0.59  % SZS output end Proof for theBenchmark
% 1.43/0.59  % (752)------------------------------
% 1.43/0.59  % (752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.59  % (752)Termination reason: Refutation
% 1.43/0.59  
% 1.43/0.59  % (752)Memory used [KB]: 2046
% 1.43/0.59  % (752)Time elapsed: 0.162 s
% 1.43/0.59  % (752)------------------------------
% 1.43/0.59  % (752)------------------------------
% 1.43/0.59  % (744)Success in time 0.219 s
%------------------------------------------------------------------------------
