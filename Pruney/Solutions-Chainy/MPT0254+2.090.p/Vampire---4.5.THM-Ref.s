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
% DateTime   : Thu Dec  3 12:39:25 EST 2020

% Result     : Theorem 1.86s
% Output     : Refutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 320 expanded)
%              Number of leaves         :   20 ( 102 expanded)
%              Depth                    :   14
%              Number of atoms          :  212 ( 457 expanded)
%              Number of equality atoms :  134 ( 367 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1007,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1006,f121])).

fof(f121,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f113,f110])).

fof(f110,plain,(
    ! [X6] : r1_xboole_0(k1_xboole_0,X6) ),
    inference(backward_demodulation,[],[f94,f109])).

fof(f109,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f56,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f94,plain,(
    ! [X6] : r1_xboole_0(k3_xboole_0(k1_xboole_0,X6),X6) ),
    inference(superposition,[],[f48,f80])).

fof(f80,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f47,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f48,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f55,f109])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f1006,plain,(
    r2_hidden(sK1,k1_xboole_0) ),
    inference(superposition,[],[f135,f993])).

fof(f993,plain,(
    k1_xboole_0 = k1_tarski(sK1) ),
    inference(forward_demodulation,[],[f988,f111])).

fof(f111,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f109,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f988,plain,(
    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f985,f987])).

fof(f987,plain,(
    k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f970,f41])).

fof(f41,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f31])).

fof(f31,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f970,plain,(
    sK2 = k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(superposition,[],[f634,f956])).

fof(f956,plain,(
    k1_tarski(sK1) = k4_xboole_0(sK2,k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f919,f44])).

fof(f919,plain,(
    k4_xboole_0(sK2,k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK1),k1_xboole_0) ),
    inference(superposition,[],[f622,f41])).

fof(f622,plain,(
    ! [X17,X18] : k4_xboole_0(X18,X17) = k5_xboole_0(X17,k2_xboole_0(X17,X18)) ),
    inference(superposition,[],[f402,f405])).

fof(f405,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f383,f150])).

fof(f150,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f51,f46])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f383,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f58,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f402,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f374,f80])).

fof(f374,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f58,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f634,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2 ),
    inference(forward_demodulation,[],[f612,f487])).

fof(f487,plain,(
    ! [X6,X5] : k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,X6)) = X5 ),
    inference(superposition,[],[f440,f51])).

fof(f440,plain,(
    ! [X10,X9] : k5_xboole_0(k5_xboole_0(X9,X10),X10) = X9 ),
    inference(superposition,[],[f408,f402])).

fof(f408,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f402,f47])).

fof(f612,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f405,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f985,plain,(
    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),sK2) ),
    inference(forward_demodulation,[],[f968,f984])).

fof(f984,plain,(
    k1_tarski(sK1) = k5_xboole_0(sK2,k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f967,f976])).

fof(f976,plain,(
    k1_tarski(sK1) = k3_xboole_0(sK2,k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f963,f956])).

fof(f963,plain,(
    k4_xboole_0(sK2,k1_tarski(sK1)) = k3_xboole_0(sK2,k1_tarski(sK1)) ),
    inference(superposition,[],[f52,f956])).

fof(f967,plain,(
    k3_xboole_0(sK2,k1_tarski(sK1)) = k5_xboole_0(sK2,k1_tarski(sK1)) ),
    inference(superposition,[],[f410,f956])).

fof(f410,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f402,f51])).

fof(f968,plain,(
    k3_xboole_0(k1_tarski(sK1),sK2) = k5_xboole_0(sK2,k1_tarski(sK1)) ),
    inference(superposition,[],[f411,f956])).

fof(f411,plain,(
    ! [X8,X7] : k3_xboole_0(X8,X7) = k5_xboole_0(X7,k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f402,f150])).

fof(f135,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f134,f45])).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f134,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f130,f50])).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f130,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(resolution,[],[f76,f75])).

fof(f75,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK4(X0,X1,X2,X3) != X0
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X0
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X2
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK4(X0,X1,X2,X3) != X0
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X0
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X2
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f76,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f28,f29])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:34:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (5579)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (5572)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (5588)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (5574)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (5588)Refutation not found, incomplete strategy% (5588)------------------------------
% 0.21/0.53  % (5588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5588)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5588)Memory used [KB]: 10618
% 0.21/0.53  % (5588)Time elapsed: 0.114 s
% 0.21/0.53  % (5588)------------------------------
% 0.21/0.53  % (5588)------------------------------
% 0.21/0.54  % (5580)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (5578)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (5576)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (5577)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (5575)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (5573)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (5571)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (5586)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (5586)Refutation not found, incomplete strategy% (5586)------------------------------
% 0.21/0.54  % (5586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5586)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5586)Memory used [KB]: 6140
% 0.21/0.54  % (5586)Time elapsed: 0.001 s
% 0.21/0.54  % (5586)------------------------------
% 0.21/0.54  % (5586)------------------------------
% 0.21/0.54  % (5594)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (5594)Refutation not found, incomplete strategy% (5594)------------------------------
% 0.21/0.54  % (5594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5594)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5594)Memory used [KB]: 1663
% 0.21/0.54  % (5594)Time elapsed: 0.090 s
% 0.21/0.54  % (5594)------------------------------
% 0.21/0.54  % (5594)------------------------------
% 0.21/0.55  % (5595)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (5590)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (5592)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (5593)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (5583)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (5591)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (5596)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (5587)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (5591)Refutation not found, incomplete strategy% (5591)------------------------------
% 0.21/0.55  % (5591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5591)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5591)Memory used [KB]: 10746
% 0.21/0.55  % (5591)Time elapsed: 0.138 s
% 0.21/0.55  % (5591)------------------------------
% 0.21/0.55  % (5591)------------------------------
% 0.21/0.55  % (5582)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (5601)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (5584)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (5581)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (5581)Refutation not found, incomplete strategy% (5581)------------------------------
% 0.21/0.56  % (5581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5581)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5581)Memory used [KB]: 10618
% 0.21/0.56  % (5581)Time elapsed: 0.136 s
% 0.21/0.56  % (5581)------------------------------
% 0.21/0.56  % (5581)------------------------------
% 0.21/0.56  % (5599)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (5598)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (5585)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (5597)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.57  % (5589)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.86/0.61  % (5578)Refutation found. Thanks to Tanya!
% 1.86/0.61  % SZS status Theorem for theBenchmark
% 1.86/0.61  % SZS output start Proof for theBenchmark
% 1.86/0.61  fof(f1007,plain,(
% 1.86/0.61    $false),
% 1.86/0.61    inference(subsumption_resolution,[],[f1006,f121])).
% 1.86/0.61  fof(f121,plain,(
% 1.86/0.61    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.86/0.61    inference(subsumption_resolution,[],[f113,f110])).
% 1.86/0.61  fof(f110,plain,(
% 1.86/0.61    ( ! [X6] : (r1_xboole_0(k1_xboole_0,X6)) )),
% 1.86/0.61    inference(backward_demodulation,[],[f94,f109])).
% 1.86/0.61  fof(f109,plain,(
% 1.86/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.86/0.61    inference(resolution,[],[f56,f42])).
% 1.86/0.61  fof(f42,plain,(
% 1.86/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f7])).
% 1.86/0.61  fof(f7,axiom,(
% 1.86/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.86/0.61  fof(f56,plain,(
% 1.86/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.86/0.61    inference(cnf_transformation,[],[f27])).
% 1.86/0.61  fof(f27,plain,(
% 1.86/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.86/0.61    inference(ennf_transformation,[],[f6])).
% 1.86/0.61  fof(f6,axiom,(
% 1.86/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.86/0.61  fof(f94,plain,(
% 1.86/0.61    ( ! [X6] : (r1_xboole_0(k3_xboole_0(k1_xboole_0,X6),X6)) )),
% 1.86/0.61    inference(superposition,[],[f48,f80])).
% 1.86/0.61  fof(f80,plain,(
% 1.86/0.61    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.86/0.61    inference(superposition,[],[f47,f44])).
% 1.86/0.61  fof(f44,plain,(
% 1.86/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.86/0.61    inference(cnf_transformation,[],[f9])).
% 1.86/0.61  fof(f9,axiom,(
% 1.86/0.61    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.86/0.61  fof(f47,plain,(
% 1.86/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f2])).
% 1.86/0.61  fof(f2,axiom,(
% 1.86/0.61    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.86/0.61  fof(f48,plain,(
% 1.86/0.61    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.86/0.61    inference(cnf_transformation,[],[f4])).
% 1.86/0.61  fof(f4,axiom,(
% 1.86/0.61    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 1.86/0.61  fof(f113,plain,(
% 1.86/0.61    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,X0)) )),
% 1.86/0.61    inference(superposition,[],[f55,f109])).
% 1.86/0.61  fof(f55,plain,(
% 1.86/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f34])).
% 1.86/0.61  fof(f34,plain,(
% 1.86/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.86/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f33])).
% 1.86/0.61  fof(f33,plain,(
% 1.86/0.61    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.86/0.61    introduced(choice_axiom,[])).
% 1.86/0.61  fof(f26,plain,(
% 1.86/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.86/0.61    inference(ennf_transformation,[],[f24])).
% 1.86/0.61  fof(f24,plain,(
% 1.86/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.86/0.61    inference(rectify,[],[f3])).
% 1.86/0.61  fof(f3,axiom,(
% 1.86/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.86/0.61  fof(f1006,plain,(
% 1.86/0.61    r2_hidden(sK1,k1_xboole_0)),
% 1.86/0.61    inference(superposition,[],[f135,f993])).
% 1.86/0.61  fof(f993,plain,(
% 1.86/0.61    k1_xboole_0 = k1_tarski(sK1)),
% 1.86/0.61    inference(forward_demodulation,[],[f988,f111])).
% 1.86/0.61  fof(f111,plain,(
% 1.86/0.61    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.86/0.61    inference(superposition,[],[f109,f46])).
% 1.86/0.61  fof(f46,plain,(
% 1.86/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f1])).
% 1.86/0.61  fof(f1,axiom,(
% 1.86/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.86/0.61  fof(f988,plain,(
% 1.86/0.61    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_xboole_0)),
% 1.86/0.61    inference(backward_demodulation,[],[f985,f987])).
% 1.86/0.61  fof(f987,plain,(
% 1.86/0.61    k1_xboole_0 = sK2),
% 1.86/0.61    inference(forward_demodulation,[],[f970,f41])).
% 1.86/0.61  fof(f41,plain,(
% 1.86/0.61    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2)),
% 1.86/0.61    inference(cnf_transformation,[],[f32])).
% 1.86/0.61  fof(f32,plain,(
% 1.86/0.61    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2)),
% 1.86/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f31])).
% 1.86/0.61  fof(f31,plain,(
% 1.86/0.61    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),sK2)),
% 1.86/0.61    introduced(choice_axiom,[])).
% 1.86/0.61  fof(f25,plain,(
% 1.86/0.61    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 1.86/0.61    inference(ennf_transformation,[],[f23])).
% 1.86/0.61  fof(f23,negated_conjecture,(
% 1.86/0.61    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.86/0.61    inference(negated_conjecture,[],[f22])).
% 1.86/0.61  fof(f22,conjecture,(
% 1.86/0.61    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.86/0.61  fof(f970,plain,(
% 1.86/0.61    sK2 = k2_xboole_0(k1_tarski(sK1),sK2)),
% 1.86/0.61    inference(superposition,[],[f634,f956])).
% 1.86/0.61  fof(f956,plain,(
% 1.86/0.61    k1_tarski(sK1) = k4_xboole_0(sK2,k1_tarski(sK1))),
% 1.86/0.61    inference(forward_demodulation,[],[f919,f44])).
% 1.86/0.61  fof(f919,plain,(
% 1.86/0.61    k4_xboole_0(sK2,k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK1),k1_xboole_0)),
% 1.86/0.61    inference(superposition,[],[f622,f41])).
% 1.86/0.61  fof(f622,plain,(
% 1.86/0.61    ( ! [X17,X18] : (k4_xboole_0(X18,X17) = k5_xboole_0(X17,k2_xboole_0(X17,X18))) )),
% 1.86/0.61    inference(superposition,[],[f402,f405])).
% 1.86/0.61  fof(f405,plain,(
% 1.86/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.86/0.61    inference(forward_demodulation,[],[f383,f150])).
% 1.86/0.61  fof(f150,plain,(
% 1.86/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 1.86/0.61    inference(superposition,[],[f51,f46])).
% 1.86/0.61  fof(f51,plain,(
% 1.86/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.86/0.61    inference(cnf_transformation,[],[f5])).
% 1.86/0.61  fof(f5,axiom,(
% 1.86/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.86/0.61  fof(f383,plain,(
% 1.86/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 1.86/0.61    inference(superposition,[],[f58,f53])).
% 1.86/0.61  fof(f53,plain,(
% 1.86/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.86/0.61    inference(cnf_transformation,[],[f12])).
% 1.86/0.61  fof(f12,axiom,(
% 1.86/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.86/0.61  fof(f58,plain,(
% 1.86/0.61    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.86/0.61    inference(cnf_transformation,[],[f10])).
% 1.86/0.61  fof(f10,axiom,(
% 1.86/0.61    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.86/0.61  fof(f402,plain,(
% 1.86/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.86/0.61    inference(forward_demodulation,[],[f374,f80])).
% 1.86/0.61  fof(f374,plain,(
% 1.86/0.61    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.86/0.61    inference(superposition,[],[f58,f43])).
% 1.86/0.61  fof(f43,plain,(
% 1.86/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f11])).
% 1.86/0.61  fof(f11,axiom,(
% 1.86/0.61    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.86/0.61  fof(f634,plain,(
% 1.86/0.61    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) )),
% 1.86/0.61    inference(forward_demodulation,[],[f612,f487])).
% 1.86/0.61  fof(f487,plain,(
% 1.86/0.61    ( ! [X6,X5] : (k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,X6)) = X5) )),
% 1.86/0.61    inference(superposition,[],[f440,f51])).
% 1.86/0.61  fof(f440,plain,(
% 1.86/0.61    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X9,X10),X10) = X9) )),
% 1.86/0.61    inference(superposition,[],[f408,f402])).
% 1.86/0.61  fof(f408,plain,(
% 1.86/0.61    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 1.86/0.61    inference(superposition,[],[f402,f47])).
% 1.86/0.61  fof(f612,plain,(
% 1.86/0.61    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))) )),
% 1.86/0.61    inference(superposition,[],[f405,f52])).
% 1.86/0.61  fof(f52,plain,(
% 1.86/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.86/0.61    inference(cnf_transformation,[],[f8])).
% 1.86/0.61  fof(f8,axiom,(
% 1.86/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.86/0.61  fof(f985,plain,(
% 1.86/0.61    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),sK2)),
% 1.86/0.61    inference(forward_demodulation,[],[f968,f984])).
% 1.86/0.61  fof(f984,plain,(
% 1.86/0.61    k1_tarski(sK1) = k5_xboole_0(sK2,k1_tarski(sK1))),
% 1.86/0.61    inference(forward_demodulation,[],[f967,f976])).
% 1.86/0.61  fof(f976,plain,(
% 1.86/0.61    k1_tarski(sK1) = k3_xboole_0(sK2,k1_tarski(sK1))),
% 1.86/0.61    inference(forward_demodulation,[],[f963,f956])).
% 1.86/0.61  fof(f963,plain,(
% 1.86/0.61    k4_xboole_0(sK2,k1_tarski(sK1)) = k3_xboole_0(sK2,k1_tarski(sK1))),
% 1.86/0.61    inference(superposition,[],[f52,f956])).
% 1.86/0.61  fof(f967,plain,(
% 1.86/0.61    k3_xboole_0(sK2,k1_tarski(sK1)) = k5_xboole_0(sK2,k1_tarski(sK1))),
% 1.86/0.61    inference(superposition,[],[f410,f956])).
% 1.86/0.61  fof(f410,plain,(
% 1.86/0.61    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 1.86/0.61    inference(superposition,[],[f402,f51])).
% 1.86/0.61  fof(f968,plain,(
% 1.86/0.61    k3_xboole_0(k1_tarski(sK1),sK2) = k5_xboole_0(sK2,k1_tarski(sK1))),
% 1.86/0.61    inference(superposition,[],[f411,f956])).
% 1.86/0.61  fof(f411,plain,(
% 1.86/0.61    ( ! [X8,X7] : (k3_xboole_0(X8,X7) = k5_xboole_0(X7,k4_xboole_0(X7,X8))) )),
% 1.86/0.61    inference(superposition,[],[f402,f150])).
% 1.86/0.61  fof(f135,plain,(
% 1.86/0.61    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 1.86/0.61    inference(superposition,[],[f134,f45])).
% 1.86/0.61  fof(f45,plain,(
% 1.86/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f14])).
% 1.86/0.61  fof(f14,axiom,(
% 1.86/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.86/0.61  fof(f134,plain,(
% 1.86/0.61    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 1.86/0.61    inference(superposition,[],[f130,f50])).
% 1.86/0.61  fof(f50,plain,(
% 1.86/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f15])).
% 1.86/0.61  fof(f15,axiom,(
% 1.86/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.86/0.61  fof(f130,plain,(
% 1.86/0.61    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X1,X2))) )),
% 1.86/0.61    inference(resolution,[],[f76,f75])).
% 1.86/0.61  fof(f75,plain,(
% 1.86/0.61    ( ! [X0,X5,X3,X1] : (~sP0(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 1.86/0.61    inference(equality_resolution,[],[f61])).
% 1.86/0.61  fof(f61,plain,(
% 1.86/0.61    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 1.86/0.61    inference(cnf_transformation,[],[f39])).
% 1.86/0.61  fof(f39,plain,(
% 1.86/0.61    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK4(X0,X1,X2,X3) != X0 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X0 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X2 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.86/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 1.86/0.61  fof(f38,plain,(
% 1.86/0.61    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X0 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X0 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X2 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.86/0.61    introduced(choice_axiom,[])).
% 1.86/0.61  fof(f37,plain,(
% 1.86/0.61    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.86/0.61    inference(rectify,[],[f36])).
% 1.86/0.61  fof(f36,plain,(
% 1.86/0.61    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.86/0.61    inference(flattening,[],[f35])).
% 1.86/0.61  fof(f35,plain,(
% 1.86/0.61    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.86/0.61    inference(nnf_transformation,[],[f29])).
% 1.86/0.61  fof(f29,plain,(
% 1.86/0.61    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.86/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.86/0.61  fof(f76,plain,(
% 1.86/0.61    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 1.86/0.61    inference(equality_resolution,[],[f68])).
% 1.86/0.61  fof(f68,plain,(
% 1.86/0.61    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.86/0.61    inference(cnf_transformation,[],[f40])).
% 1.86/0.61  fof(f40,plain,(
% 1.86/0.61    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.86/0.61    inference(nnf_transformation,[],[f30])).
% 1.86/0.61  fof(f30,plain,(
% 1.86/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 1.86/0.61    inference(definition_folding,[],[f28,f29])).
% 1.86/0.61  fof(f28,plain,(
% 1.86/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.86/0.61    inference(ennf_transformation,[],[f13])).
% 1.86/0.61  fof(f13,axiom,(
% 1.86/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.86/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.86/0.61  % SZS output end Proof for theBenchmark
% 1.86/0.61  % (5578)------------------------------
% 1.86/0.61  % (5578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.86/0.61  % (5578)Termination reason: Refutation
% 1.86/0.61  
% 1.86/0.61  % (5578)Memory used [KB]: 6908
% 1.86/0.61  % (5578)Time elapsed: 0.166 s
% 1.86/0.61  % (5578)------------------------------
% 1.86/0.61  % (5578)------------------------------
% 1.86/0.61  % (5570)Success in time 0.243 s
%------------------------------------------------------------------------------
