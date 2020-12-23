%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:45 EST 2020

% Result     : Theorem 1.98s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 241 expanded)
%              Number of leaves         :   20 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :  150 ( 362 expanded)
%              Number of equality atoms :   77 ( 252 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2303,plain,(
    $false ),
    inference(global_subsumption,[],[f67,f2285])).

fof(f2285,plain,(
    sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(backward_demodulation,[],[f266,f2164])).

fof(f2164,plain,(
    ! [X0] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(unit_resulting_resolution,[],[f1328,f701])).

fof(f701,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f665,f36])).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f665,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f66,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f71,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1328,plain,(
    ! [X0] : r1_xboole_0(sK0,k4_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(unit_resulting_resolution,[],[f255,f90])).

fof(f90,plain,(
    ! [X0] :
      ( r2_hidden(sK1,X0)
      | r1_xboole_0(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( r2_hidden(sK1,X0)
      | r1_xboole_0(sK0,X0)
      | r1_xboole_0(sK0,X0) ) ),
    inference(superposition,[],[f48,f85])).

fof(f85,plain,(
    ! [X0] :
      ( sK1 = sK4(sK0,X0)
      | r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f47,f32])).

fof(f32,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f255,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(global_subsumption,[],[f138,f253])).

fof(f253,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
      | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(resolution,[],[f74,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f65])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f138,plain,(
    ! [X1] : k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(backward_demodulation,[],[f77,f134])).

fof(f134,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f133,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f133,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f66,f68])).

fof(f68,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f39,f43])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f77,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f54,f65,f65,f65])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f266,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(unit_resulting_resolution,[],[f81,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f65,f43,f65])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f81,plain,(
    r2_hidden(sK1,sK0) ),
    inference(backward_demodulation,[],[f78,f80])).

fof(f80,plain,(
    sK1 = sK2(sK0) ),
    inference(global_subsumption,[],[f34,f79])).

fof(f79,plain,
    ( k1_xboole_0 = sK0
    | sK1 = sK2(sK0) ),
    inference(resolution,[],[f38,f32])).

fof(f34,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    r2_hidden(sK2(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f34,f38])).

fof(f67,plain,(
    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f33,f65])).

fof(f33,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:12:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (11856)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (11853)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (11849)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (11856)Refutation not found, incomplete strategy% (11856)------------------------------
% 0.20/0.51  % (11856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11848)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (11856)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (11856)Memory used [KB]: 10618
% 0.20/0.52  % (11856)Time elapsed: 0.097 s
% 0.20/0.52  % (11856)------------------------------
% 0.20/0.52  % (11856)------------------------------
% 0.20/0.52  % (11865)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (11857)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (11862)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (11871)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (11863)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (11857)Refutation not found, incomplete strategy% (11857)------------------------------
% 0.20/0.53  % (11857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11857)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11857)Memory used [KB]: 10618
% 0.20/0.53  % (11857)Time elapsed: 0.118 s
% 0.20/0.53  % (11857)------------------------------
% 0.20/0.53  % (11857)------------------------------
% 0.20/0.53  % (11864)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (11851)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (11869)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (11864)Refutation not found, incomplete strategy% (11864)------------------------------
% 0.20/0.53  % (11864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11864)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11864)Memory used [KB]: 10618
% 0.20/0.53  % (11864)Time elapsed: 0.122 s
% 0.20/0.53  % (11864)------------------------------
% 0.20/0.53  % (11864)------------------------------
% 1.36/0.54  % (11847)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.54  % (11847)Refutation not found, incomplete strategy% (11847)------------------------------
% 1.36/0.54  % (11847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (11847)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (11847)Memory used [KB]: 1663
% 1.36/0.54  % (11847)Time elapsed: 0.119 s
% 1.36/0.54  % (11847)------------------------------
% 1.36/0.54  % (11847)------------------------------
% 1.36/0.54  % (11855)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.36/0.54  % (11858)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.36/0.54  % (11860)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.54  % (11854)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.54  % (11858)Refutation not found, incomplete strategy% (11858)------------------------------
% 1.36/0.54  % (11858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (11858)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (11858)Memory used [KB]: 10618
% 1.36/0.54  % (11858)Time elapsed: 0.126 s
% 1.36/0.54  % (11858)------------------------------
% 1.36/0.54  % (11858)------------------------------
% 1.36/0.54  % (11868)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.55  % (11850)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.55  % (11870)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.55  % (11861)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.51/0.55  % (11875)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.51/0.55  % (11874)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.51/0.56  % (11852)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.51/0.56  % (11876)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.51/0.56  % (11872)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.51/0.56  % (11867)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.51/0.57  % (11873)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.51/0.57  % (11859)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.51/0.57  % (11866)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.98/0.64  % (11871)Refutation found. Thanks to Tanya!
% 1.98/0.64  % SZS status Theorem for theBenchmark
% 1.98/0.64  % (11880)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 1.98/0.64  % (11879)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.98/0.65  % SZS output start Proof for theBenchmark
% 1.98/0.65  fof(f2303,plain,(
% 1.98/0.65    $false),
% 1.98/0.65    inference(global_subsumption,[],[f67,f2285])).
% 1.98/0.65  fof(f2285,plain,(
% 1.98/0.65    sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 1.98/0.65    inference(backward_demodulation,[],[f266,f2164])).
% 1.98/0.65  fof(f2164,plain,(
% 1.98/0.65    ( ! [X0] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) )),
% 1.98/0.65    inference(unit_resulting_resolution,[],[f1328,f701])).
% 1.98/0.65  fof(f701,plain,(
% 1.98/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.98/0.65    inference(forward_demodulation,[],[f665,f36])).
% 1.98/0.65  fof(f36,plain,(
% 1.98/0.65    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.98/0.65    inference(cnf_transformation,[],[f9])).
% 1.98/0.65  fof(f9,axiom,(
% 1.98/0.65    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.98/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.98/0.65  fof(f665,plain,(
% 1.98/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_xboole_0) | ~r1_xboole_0(X0,X1)) )),
% 1.98/0.65    inference(superposition,[],[f66,f119])).
% 1.98/0.65  fof(f119,plain,(
% 1.98/0.65    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.98/0.65    inference(resolution,[],[f71,f38])).
% 1.98/0.65  fof(f38,plain,(
% 1.98/0.65    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.98/0.65    inference(cnf_transformation,[],[f27])).
% 1.98/0.65  fof(f27,plain,(
% 1.98/0.65    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.98/0.65    inference(ennf_transformation,[],[f5])).
% 1.98/0.65  fof(f5,axiom,(
% 1.98/0.65    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.98/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.98/0.65  fof(f71,plain,(
% 1.98/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.98/0.65    inference(definition_unfolding,[],[f44,f43])).
% 1.98/0.65  fof(f43,plain,(
% 1.98/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.98/0.65    inference(cnf_transformation,[],[f8])).
% 1.98/0.65  fof(f8,axiom,(
% 1.98/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.98/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.98/0.65  fof(f44,plain,(
% 1.98/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.98/0.65    inference(cnf_transformation,[],[f28])).
% 1.98/0.65  fof(f28,plain,(
% 1.98/0.65    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.98/0.65    inference(ennf_transformation,[],[f24])).
% 1.98/0.65  fof(f24,plain,(
% 1.98/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.98/0.65    inference(rectify,[],[f4])).
% 1.98/0.65  fof(f4,axiom,(
% 1.98/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.98/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.98/0.65  fof(f66,plain,(
% 1.98/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.98/0.65    inference(definition_unfolding,[],[f42,f43])).
% 1.98/0.65  fof(f42,plain,(
% 1.98/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.98/0.65    inference(cnf_transformation,[],[f6])).
% 1.98/0.65  fof(f6,axiom,(
% 1.98/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.98/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.98/0.65  fof(f1328,plain,(
% 1.98/0.65    ( ! [X0] : (r1_xboole_0(sK0,k4_xboole_0(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) )),
% 1.98/0.65    inference(unit_resulting_resolution,[],[f255,f90])).
% 1.98/0.65  fof(f90,plain,(
% 1.98/0.65    ( ! [X0] : (r2_hidden(sK1,X0) | r1_xboole_0(sK0,X0)) )),
% 1.98/0.65    inference(duplicate_literal_removal,[],[f89])).
% 1.98/0.65  fof(f89,plain,(
% 1.98/0.65    ( ! [X0] : (r2_hidden(sK1,X0) | r1_xboole_0(sK0,X0) | r1_xboole_0(sK0,X0)) )),
% 1.98/0.65    inference(superposition,[],[f48,f85])).
% 1.98/0.65  fof(f85,plain,(
% 1.98/0.65    ( ! [X0] : (sK1 = sK4(sK0,X0) | r1_xboole_0(sK0,X0)) )),
% 1.98/0.65    inference(resolution,[],[f47,f32])).
% 1.98/0.65  fof(f32,plain,(
% 1.98/0.65    ( ! [X2] : (~r2_hidden(X2,sK0) | sK1 = X2) )),
% 1.98/0.65    inference(cnf_transformation,[],[f26])).
% 1.98/0.65  fof(f26,plain,(
% 1.98/0.65    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.98/0.65    inference(ennf_transformation,[],[f22])).
% 1.98/0.65  fof(f22,negated_conjecture,(
% 1.98/0.65    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.98/0.65    inference(negated_conjecture,[],[f21])).
% 1.98/0.65  fof(f21,conjecture,(
% 1.98/0.65    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.98/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 1.98/0.65  fof(f47,plain,(
% 1.98/0.65    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.98/0.65    inference(cnf_transformation,[],[f29])).
% 1.98/0.66  fof(f29,plain,(
% 1.98/0.66    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.98/0.66    inference(ennf_transformation,[],[f25])).
% 1.98/0.66  fof(f25,plain,(
% 1.98/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.98/0.66    inference(rectify,[],[f3])).
% 1.98/0.66  fof(f3,axiom,(
% 1.98/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.98/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.98/0.66  fof(f48,plain,(
% 1.98/0.66    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.98/0.66    inference(cnf_transformation,[],[f29])).
% 1.98/0.66  fof(f255,plain,(
% 1.98/0.66    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 1.98/0.66    inference(global_subsumption,[],[f138,f253])).
% 1.98/0.66  fof(f253,plain,(
% 1.98/0.66    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.98/0.66    inference(resolution,[],[f74,f50])).
% 1.98/0.66  fof(f50,plain,(
% 1.98/0.66    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 1.98/0.66    inference(cnf_transformation,[],[f31])).
% 1.98/0.66  fof(f31,plain,(
% 1.98/0.66    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 1.98/0.66    inference(ennf_transformation,[],[f7])).
% 1.98/0.66  fof(f7,axiom,(
% 1.98/0.66    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 1.98/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).
% 1.98/0.66  fof(f74,plain,(
% 1.98/0.66    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.98/0.66    inference(definition_unfolding,[],[f51,f65])).
% 1.98/0.66  fof(f65,plain,(
% 1.98/0.66    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.98/0.66    inference(definition_unfolding,[],[f37,f64])).
% 1.98/0.66  fof(f64,plain,(
% 1.98/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.98/0.66    inference(definition_unfolding,[],[f41,f63])).
% 1.98/0.66  fof(f63,plain,(
% 1.98/0.66    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.98/0.66    inference(definition_unfolding,[],[f55,f62])).
% 1.98/0.66  fof(f62,plain,(
% 1.98/0.66    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.98/0.66    inference(definition_unfolding,[],[f56,f61])).
% 1.98/0.66  fof(f61,plain,(
% 1.98/0.66    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.98/0.66    inference(definition_unfolding,[],[f57,f60])).
% 1.98/0.66  fof(f60,plain,(
% 1.98/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.98/0.66    inference(definition_unfolding,[],[f58,f59])).
% 1.98/0.66  fof(f59,plain,(
% 1.98/0.66    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.98/0.66    inference(cnf_transformation,[],[f17])).
% 1.98/0.66  fof(f17,axiom,(
% 1.98/0.66    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.98/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.98/0.66  fof(f58,plain,(
% 1.98/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.98/0.66    inference(cnf_transformation,[],[f16])).
% 1.98/0.66  fof(f16,axiom,(
% 1.98/0.66    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.98/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.98/0.66  fof(f57,plain,(
% 1.98/0.66    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.98/0.66    inference(cnf_transformation,[],[f15])).
% 1.98/0.66  fof(f15,axiom,(
% 1.98/0.66    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.98/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.98/0.66  fof(f56,plain,(
% 1.98/0.66    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.98/0.66    inference(cnf_transformation,[],[f14])).
% 1.98/0.66  fof(f14,axiom,(
% 1.98/0.66    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.98/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.98/0.66  fof(f55,plain,(
% 1.98/0.66    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.98/0.66    inference(cnf_transformation,[],[f13])).
% 1.98/0.66  fof(f13,axiom,(
% 1.98/0.66    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.98/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.98/0.66  fof(f41,plain,(
% 1.98/0.66    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.98/0.66    inference(cnf_transformation,[],[f12])).
% 1.98/0.66  fof(f12,axiom,(
% 1.98/0.66    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.98/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.98/0.66  fof(f37,plain,(
% 1.98/0.66    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.98/0.66    inference(cnf_transformation,[],[f11])).
% 1.98/0.66  fof(f11,axiom,(
% 1.98/0.66    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.98/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.98/0.66  fof(f51,plain,(
% 1.98/0.66    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.98/0.66    inference(cnf_transformation,[],[f18])).
% 1.98/0.66  fof(f18,axiom,(
% 1.98/0.66    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.98/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.98/0.66  fof(f138,plain,(
% 1.98/0.66    ( ! [X1] : (k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 1.98/0.66    inference(backward_demodulation,[],[f77,f134])).
% 1.98/0.66  fof(f134,plain,(
% 1.98/0.66    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.98/0.66    inference(forward_demodulation,[],[f133,f35])).
% 1.98/0.66  fof(f35,plain,(
% 1.98/0.66    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.98/0.66    inference(cnf_transformation,[],[f10])).
% 1.98/0.66  fof(f10,axiom,(
% 1.98/0.66    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.98/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.98/0.66  fof(f133,plain,(
% 1.98/0.66    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 1.98/0.66    inference(superposition,[],[f66,f68])).
% 1.98/0.66  fof(f68,plain,(
% 1.98/0.66    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.98/0.66    inference(definition_unfolding,[],[f39,f43])).
% 1.98/0.66  fof(f39,plain,(
% 1.98/0.66    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.98/0.66    inference(cnf_transformation,[],[f23])).
% 1.98/0.66  fof(f23,plain,(
% 1.98/0.66    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.98/0.66    inference(rectify,[],[f2])).
% 1.98/0.66  fof(f2,axiom,(
% 1.98/0.66    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.98/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.98/0.66  fof(f77,plain,(
% 1.98/0.66    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 1.98/0.66    inference(equality_resolution,[],[f75])).
% 1.98/0.66  fof(f75,plain,(
% 1.98/0.66    ( ! [X0,X1] : (X0 != X1 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 1.98/0.66    inference(definition_unfolding,[],[f54,f65,f65,f65])).
% 1.98/0.66  fof(f54,plain,(
% 1.98/0.66    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.98/0.66    inference(cnf_transformation,[],[f20])).
% 1.98/0.66  fof(f20,axiom,(
% 1.98/0.66    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.98/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.98/0.66  fof(f266,plain,(
% 1.98/0.66    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 1.98/0.66    inference(unit_resulting_resolution,[],[f81,f72])).
% 1.98/0.66  fof(f72,plain,(
% 1.98/0.66    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) | ~r2_hidden(X0,X1)) )),
% 1.98/0.66    inference(definition_unfolding,[],[f49,f65,f43,f65])).
% 1.98/0.66  fof(f49,plain,(
% 1.98/0.66    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))) )),
% 1.98/0.66    inference(cnf_transformation,[],[f30])).
% 1.98/0.66  fof(f30,plain,(
% 1.98/0.66    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 1.98/0.66    inference(ennf_transformation,[],[f19])).
% 1.98/0.66  fof(f19,axiom,(
% 1.98/0.66    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 1.98/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 1.98/0.66  fof(f81,plain,(
% 1.98/0.66    r2_hidden(sK1,sK0)),
% 1.98/0.66    inference(backward_demodulation,[],[f78,f80])).
% 1.98/0.66  fof(f80,plain,(
% 1.98/0.66    sK1 = sK2(sK0)),
% 1.98/0.66    inference(global_subsumption,[],[f34,f79])).
% 1.98/0.66  fof(f79,plain,(
% 1.98/0.66    k1_xboole_0 = sK0 | sK1 = sK2(sK0)),
% 1.98/0.66    inference(resolution,[],[f38,f32])).
% 1.98/0.66  fof(f34,plain,(
% 1.98/0.66    k1_xboole_0 != sK0),
% 1.98/0.66    inference(cnf_transformation,[],[f26])).
% 1.98/0.66  fof(f78,plain,(
% 1.98/0.66    r2_hidden(sK2(sK0),sK0)),
% 1.98/0.66    inference(unit_resulting_resolution,[],[f34,f38])).
% 1.98/0.66  fof(f67,plain,(
% 1.98/0.66    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 1.98/0.66    inference(definition_unfolding,[],[f33,f65])).
% 1.98/0.66  fof(f33,plain,(
% 1.98/0.66    sK0 != k1_tarski(sK1)),
% 1.98/0.66    inference(cnf_transformation,[],[f26])).
% 1.98/0.66  % SZS output end Proof for theBenchmark
% 1.98/0.66  % (11871)------------------------------
% 1.98/0.66  % (11871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.66  % (11871)Termination reason: Refutation
% 1.98/0.66  
% 1.98/0.66  % (11871)Memory used [KB]: 7291
% 1.98/0.66  % (11871)Time elapsed: 0.217 s
% 1.98/0.66  % (11871)------------------------------
% 1.98/0.66  % (11871)------------------------------
% 1.98/0.66  % (11846)Success in time 0.297 s
%------------------------------------------------------------------------------
