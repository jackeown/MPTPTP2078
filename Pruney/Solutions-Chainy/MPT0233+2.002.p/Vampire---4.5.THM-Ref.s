%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:04 EST 2020

% Result     : Theorem 2.41s
% Output     : Refutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 104 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   16
%              Number of atoms          :  210 ( 352 expanded)
%              Number of equality atoms :  150 ( 258 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1441,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f42,f41,f1313,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_tarski(X0,X1))
      | X0 = X2
      | X1 = X2 ) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_tarski(X0,X1))
      | X0 = X2
      | X0 = X2
      | X1 = X2 ) ),
    inference(superposition,[],[f82,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f82,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k1_enumset1(X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
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
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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

fof(f1313,plain,(
    r2_hidden(sK0,k2_tarski(sK2,sK3)) ),
    inference(superposition,[],[f81,f1241])).

fof(f1241,plain,(
    k2_tarski(sK2,sK3) = k1_enumset1(sK0,sK2,sK3) ),
    inference(forward_demodulation,[],[f1240,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f1240,plain,(
    k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0) = k1_enumset1(sK0,sK2,sK3) ),
    inference(forward_demodulation,[],[f1228,f255])).

fof(f255,plain,(
    ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) ),
    inference(superposition,[],[f127,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f127,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(forward_demodulation,[],[f121,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f121,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(superposition,[],[f62,f45])).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f1228,plain,(
    k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0) = k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK0)) ),
    inference(superposition,[],[f52,f1215])).

fof(f1215,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k2_tarski(sK2,sK3)) ),
    inference(forward_demodulation,[],[f1198,f174])).

fof(f174,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f102,f173])).

fof(f173,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f171,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f171,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f54,f107])).

fof(f107,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f101,f44])).

fof(f101,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f53,f43])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f102,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f53,f46])).

fof(f46,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f1198,plain,(
    k4_xboole_0(k1_tarski(sK0),k2_tarski(sK2,sK3)) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f53,f481])).

fof(f481,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k2_tarski(sK2,sK3)) ),
    inference(resolution,[],[f304,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f304,plain,(
    r1_tarski(k1_tarski(sK0),k2_tarski(sK2,sK3)) ),
    inference(superposition,[],[f149,f51])).

fof(f51,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f149,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,k2_tarski(sK0,sK1)),k2_tarski(sK2,sK3)) ),
    inference(superposition,[],[f129,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f129,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(k2_tarski(sK0,sK1),X0),k2_tarski(sK2,sK3)) ),
    inference(resolution,[],[f120,f47])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f120,plain,(
    ! [X7] :
      ( ~ r1_tarski(X7,k2_tarski(sK0,sK1))
      | r1_tarski(X7,k2_tarski(sK2,sK3)) ) ),
    inference(resolution,[],[f60,f40])).

fof(f40,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f81,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f41,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f42,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (695)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.50  % (687)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (682)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (686)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (689)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (694)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (691)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (696)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.34/0.53  % (706)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.34/0.53  % (690)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.34/0.54  % (702)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.34/0.54  % (711)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.54  % (693)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.34/0.54  % (710)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.34/0.54  % (683)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.34/0.54  % (683)Refutation not found, incomplete strategy% (683)------------------------------
% 1.34/0.54  % (683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (683)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (683)Memory used [KB]: 1663
% 1.34/0.54  % (683)Time elapsed: 0.124 s
% 1.34/0.54  % (683)------------------------------
% 1.34/0.54  % (683)------------------------------
% 1.34/0.54  % (684)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.34/0.55  % (708)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.49/0.55  % (698)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.49/0.55  % (685)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.49/0.55  % (700)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.49/0.55  % (704)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.49/0.56  % (688)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.56  % (701)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.49/0.56  % (697)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.49/0.56  % (708)Refutation not found, incomplete strategy% (708)------------------------------
% 1.49/0.56  % (708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (707)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.49/0.56  % (708)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (708)Memory used [KB]: 6268
% 1.49/0.56  % (708)Time elapsed: 0.149 s
% 1.49/0.56  % (708)------------------------------
% 1.49/0.56  % (708)------------------------------
% 1.49/0.56  % (703)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.49/0.57  % (692)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.49/0.57  % (705)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.49/0.57  % (699)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.49/0.58  % (709)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 2.04/0.65  % (712)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.41/0.68  % (713)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.41/0.70  % (689)Refutation found. Thanks to Tanya!
% 2.41/0.70  % SZS status Theorem for theBenchmark
% 2.41/0.70  % SZS output start Proof for theBenchmark
% 2.41/0.70  fof(f1441,plain,(
% 2.41/0.70    $false),
% 2.41/0.70    inference(unit_resulting_resolution,[],[f42,f41,f1313,f135])).
% 2.41/0.70  fof(f135,plain,(
% 2.41/0.70    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_tarski(X0,X1)) | X0 = X2 | X1 = X2) )),
% 2.41/0.70    inference(duplicate_literal_removal,[],[f134])).
% 2.41/0.70  fof(f134,plain,(
% 2.41/0.70    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_tarski(X0,X1)) | X0 = X2 | X0 = X2 | X1 = X2) )),
% 2.41/0.70    inference(superposition,[],[f82,f50])).
% 2.41/0.70  fof(f50,plain,(
% 2.41/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.41/0.70    inference(cnf_transformation,[],[f16])).
% 2.41/0.70  fof(f16,axiom,(
% 2.41/0.70    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.41/0.70  fof(f82,plain,(
% 2.41/0.70    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k1_enumset1(X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 2.41/0.70    inference(equality_resolution,[],[f63])).
% 2.41/0.70  fof(f63,plain,(
% 2.41/0.70    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.41/0.70    inference(cnf_transformation,[],[f39])).
% 2.41/0.70  fof(f39,plain,(
% 2.41/0.70    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.41/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 2.41/0.70  fof(f38,plain,(
% 2.41/0.70    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 2.41/0.70    introduced(choice_axiom,[])).
% 2.41/0.70  fof(f37,plain,(
% 2.41/0.70    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.41/0.70    inference(rectify,[],[f36])).
% 2.41/0.70  fof(f36,plain,(
% 2.41/0.70    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.41/0.70    inference(flattening,[],[f35])).
% 2.41/0.70  fof(f35,plain,(
% 2.41/0.70    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.41/0.70    inference(nnf_transformation,[],[f30])).
% 2.41/0.70  fof(f30,plain,(
% 2.41/0.70    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.41/0.70    inference(ennf_transformation,[],[f13])).
% 2.41/0.70  fof(f13,axiom,(
% 2.41/0.70    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 2.41/0.70  fof(f1313,plain,(
% 2.41/0.70    r2_hidden(sK0,k2_tarski(sK2,sK3))),
% 2.41/0.70    inference(superposition,[],[f81,f1241])).
% 2.41/0.70  fof(f1241,plain,(
% 2.41/0.70    k2_tarski(sK2,sK3) = k1_enumset1(sK0,sK2,sK3)),
% 2.41/0.70    inference(forward_demodulation,[],[f1240,f44])).
% 2.41/0.70  fof(f44,plain,(
% 2.41/0.70    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.41/0.70    inference(cnf_transformation,[],[f11])).
% 2.41/0.70  fof(f11,axiom,(
% 2.41/0.70    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.41/0.70  fof(f1240,plain,(
% 2.41/0.70    k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0) = k1_enumset1(sK0,sK2,sK3)),
% 2.41/0.70    inference(forward_demodulation,[],[f1228,f255])).
% 2.41/0.70  fof(f255,plain,(
% 2.41/0.70    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3))) )),
% 2.41/0.70    inference(superposition,[],[f127,f48])).
% 2.41/0.70  fof(f48,plain,(
% 2.41/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.41/0.70    inference(cnf_transformation,[],[f1])).
% 2.41/0.70  fof(f1,axiom,(
% 2.41/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.41/0.70  fof(f127,plain,(
% 2.41/0.70    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 2.41/0.70    inference(forward_demodulation,[],[f121,f59])).
% 2.41/0.70  fof(f59,plain,(
% 2.41/0.70    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.41/0.70    inference(cnf_transformation,[],[f17])).
% 2.41/0.70  fof(f17,axiom,(
% 2.41/0.70    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.41/0.70  fof(f121,plain,(
% 2.41/0.70    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 2.41/0.70    inference(superposition,[],[f62,f45])).
% 2.41/0.70  fof(f45,plain,(
% 2.41/0.70    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.41/0.70    inference(cnf_transformation,[],[f15])).
% 2.41/0.70  fof(f15,axiom,(
% 2.41/0.70    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.41/0.70  fof(f62,plain,(
% 2.41/0.70    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 2.41/0.70    inference(cnf_transformation,[],[f14])).
% 2.41/0.70  fof(f14,axiom,(
% 2.41/0.70    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 2.41/0.70  fof(f1228,plain,(
% 2.41/0.70    k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0) = k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK0))),
% 2.41/0.70    inference(superposition,[],[f52,f1215])).
% 2.41/0.70  fof(f1215,plain,(
% 2.41/0.70    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k2_tarski(sK2,sK3))),
% 2.41/0.70    inference(forward_demodulation,[],[f1198,f174])).
% 2.41/0.70  fof(f174,plain,(
% 2.41/0.70    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 2.41/0.70    inference(backward_demodulation,[],[f102,f173])).
% 2.41/0.70  fof(f173,plain,(
% 2.41/0.70    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.41/0.70    inference(forward_demodulation,[],[f171,f43])).
% 2.41/0.70  fof(f43,plain,(
% 2.41/0.70    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.41/0.70    inference(cnf_transformation,[],[f9])).
% 2.41/0.70  fof(f9,axiom,(
% 2.41/0.70    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.41/0.70  fof(f171,plain,(
% 2.41/0.70    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 2.41/0.70    inference(superposition,[],[f54,f107])).
% 2.41/0.70  fof(f107,plain,(
% 2.41/0.70    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.41/0.70    inference(forward_demodulation,[],[f101,f44])).
% 2.41/0.70  fof(f101,plain,(
% 2.41/0.70    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 2.41/0.70    inference(superposition,[],[f53,f43])).
% 2.41/0.70  fof(f53,plain,(
% 2.41/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.41/0.70    inference(cnf_transformation,[],[f5])).
% 2.41/0.70  fof(f5,axiom,(
% 2.41/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.41/0.70  fof(f54,plain,(
% 2.41/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.41/0.70    inference(cnf_transformation,[],[f10])).
% 2.41/0.70  fof(f10,axiom,(
% 2.41/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.41/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.41/0.70  fof(f102,plain,(
% 2.41/0.70    ( ! [X1] : (k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1)) )),
% 2.41/0.70    inference(superposition,[],[f53,f46])).
% 2.41/0.70  fof(f46,plain,(
% 2.41/0.70    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.41/0.70    inference(cnf_transformation,[],[f25])).
% 2.41/0.71  fof(f25,plain,(
% 2.41/0.71    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.41/0.71    inference(rectify,[],[f3])).
% 2.41/0.71  fof(f3,axiom,(
% 2.41/0.71    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.41/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.41/0.71  fof(f1198,plain,(
% 2.41/0.71    k4_xboole_0(k1_tarski(sK0),k2_tarski(sK2,sK3)) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 2.41/0.71    inference(superposition,[],[f53,f481])).
% 2.41/0.71  fof(f481,plain,(
% 2.41/0.71    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k2_tarski(sK2,sK3))),
% 2.41/0.71    inference(resolution,[],[f304,f55])).
% 2.41/0.71  fof(f55,plain,(
% 2.41/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.41/0.71    inference(cnf_transformation,[],[f27])).
% 2.41/0.71  fof(f27,plain,(
% 2.41/0.71    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.41/0.71    inference(ennf_transformation,[],[f8])).
% 2.41/0.71  fof(f8,axiom,(
% 2.41/0.71    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.41/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.41/0.71  fof(f304,plain,(
% 2.41/0.71    r1_tarski(k1_tarski(sK0),k2_tarski(sK2,sK3))),
% 2.41/0.71    inference(superposition,[],[f149,f51])).
% 2.41/0.71  fof(f51,plain,(
% 2.41/0.71    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 2.41/0.71    inference(cnf_transformation,[],[f22])).
% 2.41/0.71  fof(f22,axiom,(
% 2.41/0.71    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 2.41/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 2.41/0.71  fof(f149,plain,(
% 2.41/0.71    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k2_tarski(sK0,sK1)),k2_tarski(sK2,sK3))) )),
% 2.41/0.71    inference(superposition,[],[f129,f49])).
% 2.41/0.71  fof(f49,plain,(
% 2.41/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.41/0.71    inference(cnf_transformation,[],[f2])).
% 2.41/0.71  fof(f2,axiom,(
% 2.41/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.41/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.41/0.71  fof(f129,plain,(
% 2.41/0.71    ( ! [X0] : (r1_tarski(k3_xboole_0(k2_tarski(sK0,sK1),X0),k2_tarski(sK2,sK3))) )),
% 2.41/0.71    inference(resolution,[],[f120,f47])).
% 2.41/0.71  fof(f47,plain,(
% 2.41/0.71    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.41/0.71    inference(cnf_transformation,[],[f6])).
% 2.41/0.71  fof(f6,axiom,(
% 2.41/0.71    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.41/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.41/0.71  fof(f120,plain,(
% 2.41/0.71    ( ! [X7] : (~r1_tarski(X7,k2_tarski(sK0,sK1)) | r1_tarski(X7,k2_tarski(sK2,sK3))) )),
% 2.41/0.71    inference(resolution,[],[f60,f40])).
% 2.41/0.71  fof(f40,plain,(
% 2.41/0.71    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 2.41/0.71    inference(cnf_transformation,[],[f32])).
% 2.41/0.71  fof(f32,plain,(
% 2.41/0.71    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 2.41/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f31])).
% 2.41/0.71  fof(f31,plain,(
% 2.41/0.71    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 2.41/0.71    introduced(choice_axiom,[])).
% 2.41/0.71  fof(f26,plain,(
% 2.41/0.71    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 2.41/0.71    inference(ennf_transformation,[],[f24])).
% 2.41/0.71  fof(f24,negated_conjecture,(
% 2.41/0.71    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 2.41/0.71    inference(negated_conjecture,[],[f23])).
% 2.41/0.71  fof(f23,conjecture,(
% 2.41/0.71    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 2.41/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 2.41/0.71  fof(f60,plain,(
% 2.41/0.71    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.41/0.71    inference(cnf_transformation,[],[f29])).
% 2.41/0.71  fof(f29,plain,(
% 2.41/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.41/0.71    inference(flattening,[],[f28])).
% 2.41/0.71  fof(f28,plain,(
% 2.41/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.41/0.71    inference(ennf_transformation,[],[f7])).
% 2.41/0.71  fof(f7,axiom,(
% 2.41/0.71    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.41/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.41/0.71  fof(f52,plain,(
% 2.41/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.41/0.71    inference(cnf_transformation,[],[f12])).
% 2.41/0.71  fof(f12,axiom,(
% 2.41/0.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.41/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.41/0.71  fof(f81,plain,(
% 2.41/0.71    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 2.41/0.71    inference(equality_resolution,[],[f80])).
% 2.41/0.71  fof(f80,plain,(
% 2.41/0.71    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 2.41/0.71    inference(equality_resolution,[],[f64])).
% 2.41/0.71  fof(f64,plain,(
% 2.41/0.71    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.41/0.71    inference(cnf_transformation,[],[f39])).
% 2.41/0.71  fof(f41,plain,(
% 2.41/0.71    sK0 != sK2),
% 2.41/0.71    inference(cnf_transformation,[],[f32])).
% 2.41/0.71  fof(f42,plain,(
% 2.41/0.71    sK0 != sK3),
% 2.41/0.71    inference(cnf_transformation,[],[f32])).
% 2.41/0.71  % SZS output end Proof for theBenchmark
% 2.41/0.71  % (689)------------------------------
% 2.41/0.71  % (689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.41/0.71  % (689)Termination reason: Refutation
% 2.41/0.71  
% 2.41/0.71  % (689)Memory used [KB]: 2942
% 2.41/0.71  % (689)Time elapsed: 0.281 s
% 2.41/0.71  % (689)------------------------------
% 2.41/0.71  % (689)------------------------------
% 2.41/0.71  % (681)Success in time 0.343 s
%------------------------------------------------------------------------------
