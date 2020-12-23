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
% DateTime   : Thu Dec  3 12:43:22 EST 2020

% Result     : Theorem 3.76s
% Output     : Refutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 305 expanded)
%              Number of leaves         :   12 (  91 expanded)
%              Depth                    :   16
%              Number of atoms          :  158 ( 559 expanded)
%              Number of equality atoms :   77 ( 331 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2273,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2256,f66])).

fof(f66,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f46,f47])).

fof(f47,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(definition_unfolding,[],[f20,f25,f45])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f27,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f36,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f37,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    k3_xboole_0(sK1,sK2) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f46,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(definition_unfolding,[],[f22,f45,f25])).

fof(f22,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f2256,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f2108,f2110])).

fof(f2110,plain,(
    r2_hidden(sK4(sK0,sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),sK0) ),
    inference(subsumption_resolution,[],[f2090,f66])).

fof(f2090,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | r2_hidden(sK4(sK0,sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),sK0) ),
    inference(resolution,[],[f1774,f388])).

fof(f388,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
      | r2_hidden(X4,sK0) ) ),
    inference(superposition,[],[f59,f366])).

fof(f366,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)) ),
    inference(forward_demodulation,[],[f344,f47])).

fof(f344,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK0)) ),
    inference(resolution,[],[f57,f21])).

fof(f21,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,X1)
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X2
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)) ) ),
    inference(definition_unfolding,[],[f29,f45,f25,f44])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X2
      | k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f34,f25])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f1774,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))
      | k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) ) ),
    inference(factoring,[],[f1719])).

fof(f1719,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK4(sK0,X8,X9),X9)
      | r2_hidden(sK4(sK0,X8,X9),k4_xboole_0(sK1,k4_xboole_0(sK1,X8)))
      | k4_xboole_0(sK0,k4_xboole_0(sK0,X8)) = X9 ) ),
    inference(duplicate_literal_removal,[],[f1675])).

fof(f1675,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK4(sK0,X8,X9),X9)
      | r2_hidden(sK4(sK0,X8,X9),k4_xboole_0(sK1,k4_xboole_0(sK1,X8)))
      | k4_xboole_0(sK0,k4_xboole_0(sK0,X8)) = X9
      | r2_hidden(sK4(sK0,X8,X9),X9)
      | k4_xboole_0(sK0,k4_xboole_0(sK0,X8)) = X9 ) ),
    inference(resolution,[],[f1040,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f31,f25])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1040,plain,(
    ! [X83,X84,X82] :
      ( ~ r2_hidden(sK4(X82,X83,X84),sK0)
      | r2_hidden(sK4(X82,X83,X84),X84)
      | r2_hidden(sK4(X82,X83,X84),k4_xboole_0(sK1,k4_xboole_0(sK1,X83)))
      | k4_xboole_0(X82,k4_xboole_0(X82,X83)) = X84 ) ),
    inference(resolution,[],[f88,f63])).

fof(f63,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f59,f61])).

fof(f61,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f48,f19])).

fof(f19,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f88,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ r2_hidden(sK4(X10,X11,X12),X13)
      | k4_xboole_0(X10,k4_xboole_0(X10,X11)) = X12
      | r2_hidden(sK4(X10,X11,X12),X12)
      | r2_hidden(sK4(X10,X11,X12),k4_xboole_0(X13,k4_xboole_0(X13,X11))) ) ),
    inference(resolution,[],[f54,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f35,f25])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f32,f25])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f2108,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),sK0)
      | k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f2107,f91])).

fof(f91,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(sK4(X4,X5,k4_xboole_0(X6,k4_xboole_0(X6,X7))),X5)
      | k4_xboole_0(X6,k4_xboole_0(X6,X7)) = k4_xboole_0(X4,k4_xboole_0(X4,X5))
      | r2_hidden(sK4(X4,X5,k4_xboole_0(X6,k4_xboole_0(X6,X7))),X7) ) ),
    inference(resolution,[],[f54,f59])).

fof(f2107,plain,(
    ! [X0] :
      ( k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0))
      | ~ r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),X0)
      | ~ r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),sK0) ) ),
    inference(duplicate_literal_removal,[],[f2086])).

fof(f2086,plain,(
    ! [X0] :
      ( k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0))
      | ~ r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),X0)
      | ~ r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),sK0)
      | k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) ) ),
    inference(resolution,[],[f1774,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f30,f25])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:39:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (10970)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (10978)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (10975)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (10986)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (10974)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.57  % (10983)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.57  % (10973)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.57  % (10991)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.58  % (10972)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.58  % (10977)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.58  % (10971)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.60  % (10992)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.60  % (10969)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.60  % (10995)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.60  % (10998)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.60  % (10984)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.60  % (10990)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.61  % (10987)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.61  % (10984)Refutation not found, incomplete strategy% (10984)------------------------------
% 0.22/0.61  % (10984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.61  % (10984)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.61  
% 0.22/0.61  % (10984)Memory used [KB]: 6140
% 0.22/0.61  % (10984)Time elapsed: 0.006 s
% 0.22/0.61  % (10984)------------------------------
% 0.22/0.61  % (10984)------------------------------
% 0.22/0.61  % (10989)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.61  % (10997)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.61  % (10982)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.61  % (10996)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.61  % (10993)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.61  % (10981)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.61  % (10976)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.62  % (10979)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.62  % (10985)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.62  % (10980)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.62  % (10988)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.62  % (10994)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 3.01/0.83  % (11036)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.01/0.84  % (10974)Time limit reached!
% 3.01/0.84  % (10974)------------------------------
% 3.01/0.84  % (10974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.01/0.84  % (10974)Termination reason: Time limit
% 3.01/0.84  
% 3.01/0.84  % (10974)Memory used [KB]: 8571
% 3.01/0.84  % (10974)Time elapsed: 0.416 s
% 3.01/0.84  % (10974)------------------------------
% 3.01/0.84  % (10974)------------------------------
% 3.76/0.88  % (10975)Refutation found. Thanks to Tanya!
% 3.76/0.88  % SZS status Theorem for theBenchmark
% 3.76/0.88  % SZS output start Proof for theBenchmark
% 3.76/0.88  fof(f2273,plain,(
% 3.76/0.88    $false),
% 3.76/0.88    inference(subsumption_resolution,[],[f2256,f66])).
% 3.76/0.88  fof(f66,plain,(
% 3.76/0.88    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 3.76/0.88    inference(superposition,[],[f46,f47])).
% 3.76/0.88  fof(f47,plain,(
% 3.76/0.88    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 3.76/0.88    inference(definition_unfolding,[],[f20,f25,f45])).
% 3.76/0.88  fof(f45,plain,(
% 3.76/0.88    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.76/0.88    inference(definition_unfolding,[],[f23,f44])).
% 3.76/0.88  fof(f44,plain,(
% 3.76/0.88    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.76/0.88    inference(definition_unfolding,[],[f24,f43])).
% 3.76/0.88  fof(f43,plain,(
% 3.76/0.88    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.76/0.88    inference(definition_unfolding,[],[f27,f42])).
% 3.76/0.88  fof(f42,plain,(
% 3.76/0.88    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.76/0.88    inference(definition_unfolding,[],[f36,f41])).
% 3.76/0.88  fof(f41,plain,(
% 3.76/0.88    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.76/0.88    inference(definition_unfolding,[],[f37,f40])).
% 3.76/0.88  fof(f40,plain,(
% 3.76/0.88    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.76/0.88    inference(definition_unfolding,[],[f38,f39])).
% 3.76/0.88  fof(f39,plain,(
% 3.76/0.88    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.76/0.88    inference(cnf_transformation,[],[f10])).
% 3.76/0.88  fof(f10,axiom,(
% 3.76/0.88    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.76/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 3.76/0.88  fof(f38,plain,(
% 3.76/0.88    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.76/0.88    inference(cnf_transformation,[],[f9])).
% 3.76/0.88  fof(f9,axiom,(
% 3.76/0.88    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.76/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 3.76/0.88  fof(f37,plain,(
% 3.76/0.88    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.76/0.88    inference(cnf_transformation,[],[f8])).
% 3.76/0.88  fof(f8,axiom,(
% 3.76/0.88    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.76/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 3.76/0.88  fof(f36,plain,(
% 3.76/0.88    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.76/0.88    inference(cnf_transformation,[],[f7])).
% 3.76/0.88  fof(f7,axiom,(
% 3.76/0.88    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.76/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 3.76/0.88  fof(f27,plain,(
% 3.76/0.88    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.76/0.88    inference(cnf_transformation,[],[f6])).
% 3.76/0.88  fof(f6,axiom,(
% 3.76/0.88    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.76/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.76/0.88  fof(f24,plain,(
% 3.76/0.88    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.76/0.88    inference(cnf_transformation,[],[f5])).
% 3.76/0.88  fof(f5,axiom,(
% 3.76/0.88    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.76/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.76/0.88  fof(f23,plain,(
% 3.76/0.88    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.76/0.88    inference(cnf_transformation,[],[f4])).
% 3.76/0.88  fof(f4,axiom,(
% 3.76/0.88    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.76/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.76/0.88  fof(f25,plain,(
% 3.76/0.88    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.76/0.88    inference(cnf_transformation,[],[f3])).
% 3.76/0.88  fof(f3,axiom,(
% 3.76/0.88    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.76/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.76/0.88  fof(f20,plain,(
% 3.76/0.88    k3_xboole_0(sK1,sK2) = k1_tarski(sK3)),
% 3.76/0.88    inference(cnf_transformation,[],[f15])).
% 3.76/0.88  fof(f15,plain,(
% 3.76/0.88    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 3.76/0.88    inference(flattening,[],[f14])).
% 3.76/0.88  fof(f14,plain,(
% 3.76/0.88    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 3.76/0.88    inference(ennf_transformation,[],[f13])).
% 3.76/0.88  fof(f13,negated_conjecture,(
% 3.76/0.88    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 3.76/0.88    inference(negated_conjecture,[],[f12])).
% 3.76/0.88  fof(f12,conjecture,(
% 3.76/0.88    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 3.76/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 3.76/0.88  fof(f46,plain,(
% 3.76/0.88    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 3.76/0.88    inference(definition_unfolding,[],[f22,f45,f25])).
% 3.76/0.88  fof(f22,plain,(
% 3.76/0.88    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 3.76/0.88    inference(cnf_transformation,[],[f15])).
% 3.76/0.88  fof(f2256,plain,(
% 3.76/0.88    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 3.76/0.88    inference(resolution,[],[f2108,f2110])).
% 3.76/0.88  fof(f2110,plain,(
% 3.76/0.88    r2_hidden(sK4(sK0,sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),sK0)),
% 3.76/0.88    inference(subsumption_resolution,[],[f2090,f66])).
% 3.76/0.88  fof(f2090,plain,(
% 3.76/0.88    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | r2_hidden(sK4(sK0,sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),sK0)),
% 3.76/0.88    inference(resolution,[],[f1774,f388])).
% 3.76/0.88  fof(f388,plain,(
% 3.76/0.88    ( ! [X4] : (~r2_hidden(X4,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | r2_hidden(X4,sK0)) )),
% 3.76/0.88    inference(superposition,[],[f59,f366])).
% 3.76/0.88  fof(f366,plain,(
% 3.76/0.88    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0))),
% 3.76/0.88    inference(forward_demodulation,[],[f344,f47])).
% 3.76/0.88  fof(f344,plain,(
% 3.76/0.88    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK0))),
% 3.76/0.88    inference(resolution,[],[f57,f21])).
% 3.76/0.88  fof(f21,plain,(
% 3.76/0.88    r2_hidden(sK3,sK0)),
% 3.76/0.88    inference(cnf_transformation,[],[f15])).
% 3.76/0.88  fof(f57,plain,(
% 3.76/0.88    ( ! [X2,X1] : (~r2_hidden(X2,X1) | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X1))) )),
% 3.76/0.88    inference(equality_resolution,[],[f49])).
% 3.76/0.88  fof(f49,plain,(
% 3.76/0.88    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 != X2 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1))) )),
% 3.76/0.88    inference(definition_unfolding,[],[f29,f45,f25,f44])).
% 3.76/0.88  fof(f29,plain,(
% 3.76/0.88    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 != X2 | k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)) )),
% 3.76/0.88    inference(cnf_transformation,[],[f18])).
% 3.76/0.88  fof(f18,plain,(
% 3.76/0.88    ! [X0,X1,X2] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 3.76/0.88    inference(flattening,[],[f17])).
% 3.76/0.88  fof(f17,plain,(
% 3.76/0.88    ! [X0,X1,X2] : ((k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))) | ~r2_hidden(X0,X1))),
% 3.76/0.88    inference(ennf_transformation,[],[f11])).
% 3.76/0.88  fof(f11,axiom,(
% 3.76/0.88    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 3.76/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 3.76/0.88  fof(f59,plain,(
% 3.76/0.88    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r2_hidden(X3,X1)) )),
% 3.76/0.88    inference(equality_resolution,[],[f52])).
% 3.76/0.88  fof(f52,plain,(
% 3.76/0.88    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 3.76/0.88    inference(definition_unfolding,[],[f34,f25])).
% 3.76/0.88  fof(f34,plain,(
% 3.76/0.88    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.76/0.88    inference(cnf_transformation,[],[f1])).
% 3.76/0.88  fof(f1,axiom,(
% 3.76/0.88    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.76/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 3.76/0.88  fof(f1774,plain,(
% 3.76/0.88    ( ! [X0] : (r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) | k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) )),
% 3.76/0.88    inference(factoring,[],[f1719])).
% 3.76/0.88  fof(f1719,plain,(
% 3.76/0.88    ( ! [X8,X9] : (r2_hidden(sK4(sK0,X8,X9),X9) | r2_hidden(sK4(sK0,X8,X9),k4_xboole_0(sK1,k4_xboole_0(sK1,X8))) | k4_xboole_0(sK0,k4_xboole_0(sK0,X8)) = X9) )),
% 3.76/0.88    inference(duplicate_literal_removal,[],[f1675])).
% 3.76/0.88  fof(f1675,plain,(
% 3.76/0.88    ( ! [X8,X9] : (r2_hidden(sK4(sK0,X8,X9),X9) | r2_hidden(sK4(sK0,X8,X9),k4_xboole_0(sK1,k4_xboole_0(sK1,X8))) | k4_xboole_0(sK0,k4_xboole_0(sK0,X8)) = X9 | r2_hidden(sK4(sK0,X8,X9),X9) | k4_xboole_0(sK0,k4_xboole_0(sK0,X8)) = X9) )),
% 3.76/0.88    inference(resolution,[],[f1040,f55])).
% 3.76/0.88  fof(f55,plain,(
% 3.76/0.88    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 3.76/0.88    inference(definition_unfolding,[],[f31,f25])).
% 3.76/0.88  fof(f31,plain,(
% 3.76/0.88    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 3.76/0.88    inference(cnf_transformation,[],[f1])).
% 3.76/0.88  fof(f1040,plain,(
% 3.76/0.88    ( ! [X83,X84,X82] : (~r2_hidden(sK4(X82,X83,X84),sK0) | r2_hidden(sK4(X82,X83,X84),X84) | r2_hidden(sK4(X82,X83,X84),k4_xboole_0(sK1,k4_xboole_0(sK1,X83))) | k4_xboole_0(X82,k4_xboole_0(X82,X83)) = X84) )),
% 3.76/0.88    inference(resolution,[],[f88,f63])).
% 3.76/0.88  fof(f63,plain,(
% 3.76/0.88    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 3.76/0.88    inference(superposition,[],[f59,f61])).
% 3.76/0.88  fof(f61,plain,(
% 3.76/0.88    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 3.76/0.88    inference(resolution,[],[f48,f19])).
% 3.76/0.88  fof(f19,plain,(
% 3.76/0.88    r1_tarski(sK0,sK1)),
% 3.76/0.88    inference(cnf_transformation,[],[f15])).
% 3.76/0.88  fof(f48,plain,(
% 3.76/0.88    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 3.76/0.88    inference(definition_unfolding,[],[f26,f25])).
% 3.76/0.88  fof(f26,plain,(
% 3.76/0.88    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 3.76/0.88    inference(cnf_transformation,[],[f16])).
% 3.76/0.88  fof(f16,plain,(
% 3.76/0.88    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.76/0.88    inference(ennf_transformation,[],[f2])).
% 3.76/0.88  fof(f2,axiom,(
% 3.76/0.88    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.76/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.76/0.88  fof(f88,plain,(
% 3.76/0.88    ( ! [X12,X10,X13,X11] : (~r2_hidden(sK4(X10,X11,X12),X13) | k4_xboole_0(X10,k4_xboole_0(X10,X11)) = X12 | r2_hidden(sK4(X10,X11,X12),X12) | r2_hidden(sK4(X10,X11,X12),k4_xboole_0(X13,k4_xboole_0(X13,X11)))) )),
% 3.76/0.88    inference(resolution,[],[f54,f58])).
% 3.76/0.88  fof(f58,plain,(
% 3.76/0.88    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.76/0.88    inference(equality_resolution,[],[f51])).
% 3.76/0.88  fof(f51,plain,(
% 3.76/0.88    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 3.76/0.88    inference(definition_unfolding,[],[f35,f25])).
% 3.76/0.88  fof(f35,plain,(
% 3.76/0.88    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.76/0.88    inference(cnf_transformation,[],[f1])).
% 3.76/0.88  fof(f54,plain,(
% 3.76/0.88    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 3.76/0.88    inference(definition_unfolding,[],[f32,f25])).
% 3.76/0.88  fof(f32,plain,(
% 3.76/0.88    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 3.76/0.88    inference(cnf_transformation,[],[f1])).
% 3.76/0.88  fof(f2108,plain,(
% 3.76/0.88    ( ! [X0] : (~r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),sK0) | k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) )),
% 3.76/0.88    inference(subsumption_resolution,[],[f2107,f91])).
% 3.76/0.88  fof(f91,plain,(
% 3.76/0.88    ( ! [X6,X4,X7,X5] : (r2_hidden(sK4(X4,X5,k4_xboole_0(X6,k4_xboole_0(X6,X7))),X5) | k4_xboole_0(X6,k4_xboole_0(X6,X7)) = k4_xboole_0(X4,k4_xboole_0(X4,X5)) | r2_hidden(sK4(X4,X5,k4_xboole_0(X6,k4_xboole_0(X6,X7))),X7)) )),
% 3.76/0.88    inference(resolution,[],[f54,f59])).
% 3.76/0.88  fof(f2107,plain,(
% 3.76/0.88    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) | ~r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),X0) | ~r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),sK0)) )),
% 3.76/0.88    inference(duplicate_literal_removal,[],[f2086])).
% 3.76/0.88  fof(f2086,plain,(
% 3.76/0.88    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) | ~r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),X0) | ~r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),sK0) | k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) )),
% 3.76/0.88    inference(resolution,[],[f1774,f56])).
% 3.76/0.88  fof(f56,plain,(
% 3.76/0.88    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 3.76/0.88    inference(definition_unfolding,[],[f30,f25])).
% 3.76/0.88  fof(f30,plain,(
% 3.76/0.88    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 3.76/0.88    inference(cnf_transformation,[],[f1])).
% 3.76/0.88  % SZS output end Proof for theBenchmark
% 3.76/0.88  % (10975)------------------------------
% 3.76/0.88  % (10975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.76/0.88  % (10975)Termination reason: Refutation
% 3.76/0.88  
% 3.76/0.88  % (10975)Memory used [KB]: 9850
% 3.76/0.88  % (10975)Time elapsed: 0.429 s
% 3.76/0.88  % (10975)------------------------------
% 3.76/0.88  % (10975)------------------------------
% 3.76/0.88  % (10968)Success in time 0.516 s
%------------------------------------------------------------------------------
