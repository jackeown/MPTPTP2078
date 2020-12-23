%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:59 EST 2020

% Result     : Theorem 2.75s
% Output     : Refutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :  146 (20664 expanded)
%              Number of leaves         :   24 (7003 expanded)
%              Depth                    :   41
%              Number of atoms          :  271 (22371 expanded)
%              Number of equality atoms :  219 (20584 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f892,plain,(
    $false ),
    inference(subsumption_resolution,[],[f891,f39])).

fof(f39,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f891,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f874,f94])).

fof(f94,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f58,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f65,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f36,plain,(
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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f874,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))
      | sK1 = X5 ) ),
    inference(duplicate_literal_removal,[],[f873])).

fof(f873,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))
      | sK1 = X5
      | sK1 = X5
      | sK1 = X5 ) ),
    inference(superposition,[],[f95,f802])).

fof(f802,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) ),
    inference(forward_demodulation,[],[f801,f100])).

fof(f100,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) ),
    inference(forward_demodulation,[],[f97,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f52,f72,f72])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

fof(f97,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f80,f96])).

fof(f96,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f75,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f75,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f38,f74,f74])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f72])).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k3_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)))) ),
    inference(definition_unfolding,[],[f56,f71,f68,f72,f74])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f49,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f801,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f796,f40])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f796,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) ),
    inference(superposition,[],[f706,f672])).

fof(f672,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f671,f475])).

fof(f475,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(forward_demodulation,[],[f473,f128])).

fof(f128,plain,(
    k1_xboole_0 = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) ),
    inference(resolution,[],[f117,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f117,plain,(
    r1_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) ),
    inference(superposition,[],[f77,f110])).

fof(f110,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f106,f105])).

fof(f105,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f80,f101])).

fof(f101,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(forward_demodulation,[],[f98,f100])).

fof(f98,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f78,f96])).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f46,f68])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f106,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f78,f101])).

fof(f77,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f44,f48])).

fof(f44,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f473,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) ),
    inference(backward_demodulation,[],[f214,f471])).

fof(f471,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f470,f362])).

fof(f362,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) ),
    inference(superposition,[],[f263,f105])).

fof(f263,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),X0)) ),
    inference(superposition,[],[f222,f115])).

fof(f115,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),X0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) ),
    inference(forward_demodulation,[],[f114,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f114,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),X0) ),
    inference(superposition,[],[f54,f100])).

fof(f222,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) ),
    inference(forward_demodulation,[],[f221,f54])).

fof(f221,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0) ),
    inference(superposition,[],[f54,f193])).

fof(f193,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f189,f43])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f189,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f139,f80])).

fof(f139,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) ),
    inference(forward_demodulation,[],[f138,f54])).

fof(f138,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),X0) ),
    inference(superposition,[],[f54,f105])).

fof(f470,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f466,f43])).

fof(f466,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f363,f76])).

fof(f76,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f42,f68])).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f363,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),X0)) ),
    inference(superposition,[],[f263,f139])).

fof(f214,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f213,f40])).

fof(f213,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f211,f54])).

fof(f211,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k1_xboole_0))) ),
    inference(superposition,[],[f78,f166])).

fof(f166,plain,(
    k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))) ),
    inference(superposition,[],[f128,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f671,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f649,f311])).

fof(f311,plain,(
    ! [X0,X1] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0,X1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0,X1)) ),
    inference(superposition,[],[f253,f80])).

fof(f253,plain,(
    ! [X2,X1] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1),X2)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1),X2)) ),
    inference(forward_demodulation,[],[f252,f54])).

fof(f252,plain,(
    ! [X2,X1] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1),X2)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),X2) ),
    inference(superposition,[],[f54,f223])).

fof(f223,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)) ),
    inference(superposition,[],[f175,f80])).

fof(f175,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) ),
    inference(forward_demodulation,[],[f174,f54])).

fof(f174,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0) ),
    inference(superposition,[],[f54,f153])).

fof(f153,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f149,f43])).

fof(f149,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f115,f80])).

fof(f649,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f620,f100])).

fof(f620,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f54,f490])).

fof(f490,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f489,f113])).

fof(f113,plain,(
    k1_xboole_0 = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(resolution,[],[f109,f51])).

fof(f109,plain,(
    r1_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(superposition,[],[f77,f101])).

fof(f489,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(forward_demodulation,[],[f483,f40])).

fof(f483,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f346,f475])).

fof(f346,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)))) ),
    inference(backward_demodulation,[],[f325,f337])).

fof(f337,plain,(
    ! [X6,X7,X5] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X5,X6),X7)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X5,X6),X7)) ),
    inference(forward_demodulation,[],[f336,f54])).

fof(f336,plain,(
    ! [X6,X7,X5] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X5,X6),X7)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X5,X6)),X7) ),
    inference(superposition,[],[f54,f311])).

fof(f325,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)))) ),
    inference(backward_demodulation,[],[f180,f311])).

fof(f180,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f179,f40])).

fof(f179,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f177,f54])).

fof(f177,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k1_xboole_0))) ),
    inference(superposition,[],[f78,f129])).

fof(f129,plain,(
    k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f113,f45])).

fof(f706,plain,(
    ! [X6] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X6) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,X6)) ),
    inference(backward_demodulation,[],[f654,f705])).

fof(f705,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) ),
    inference(superposition,[],[f54,f675])).

fof(f675,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f662,f40])).

fof(f662,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f620,f490])).

fof(f654,plain,(
    ! [X6] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X6)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,X6)) ),
    inference(superposition,[],[f620,f620])).

fof(f95,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f57,f72])).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:03:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (15317)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (15309)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (15301)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (15301)Refutation not found, incomplete strategy% (15301)------------------------------
% 0.21/0.55  % (15301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15301)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15301)Memory used [KB]: 10618
% 0.21/0.55  % (15301)Time elapsed: 0.120 s
% 0.21/0.55  % (15301)------------------------------
% 0.21/0.55  % (15301)------------------------------
% 1.62/0.58  % (15312)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.62/0.58  % (15304)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.62/0.58  % (15290)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.62/0.58  % (15290)Refutation not found, incomplete strategy% (15290)------------------------------
% 1.62/0.58  % (15290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.58  % (15290)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.58  
% 1.62/0.58  % (15290)Memory used [KB]: 1663
% 1.62/0.58  % (15290)Time elapsed: 0.156 s
% 1.62/0.58  % (15290)------------------------------
% 1.62/0.58  % (15290)------------------------------
% 1.62/0.58  % (15305)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.62/0.58  % (15294)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.62/0.58  % (15305)Refutation not found, incomplete strategy% (15305)------------------------------
% 1.62/0.58  % (15305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.58  % (15305)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.58  
% 1.62/0.58  % (15305)Memory used [KB]: 6140
% 1.62/0.58  % (15305)Time elapsed: 0.168 s
% 1.62/0.58  % (15305)------------------------------
% 1.62/0.58  % (15305)------------------------------
% 1.62/0.59  % (15291)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.62/0.59  % (15297)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.62/0.59  % (15295)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.62/0.59  % (15296)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.62/0.59  % (15313)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.62/0.59  % (15292)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.62/0.60  % (15314)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.62/0.60  % (15318)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.62/0.60  % (15306)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.62/0.60  % (15300)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.62/0.60  % (15300)Refutation not found, incomplete strategy% (15300)------------------------------
% 1.62/0.60  % (15300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.60  % (15300)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.60  
% 1.62/0.60  % (15300)Memory used [KB]: 10618
% 1.62/0.60  % (15300)Time elapsed: 0.177 s
% 1.62/0.60  % (15300)------------------------------
% 1.62/0.60  % (15300)------------------------------
% 1.62/0.60  % (15315)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.62/0.61  % (15316)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.62/0.61  % (15307)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.62/0.61  % (15310)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.62/0.62  % (15308)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.62/0.62  % (15293)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.62/0.63  % (15302)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.62/0.63  % (15303)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.62/0.63  % (15298)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.62/0.63  % (15307)Refutation not found, incomplete strategy% (15307)------------------------------
% 1.62/0.63  % (15307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.63  % (15307)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.63  
% 1.62/0.63  % (15307)Memory used [KB]: 10618
% 1.62/0.63  % (15307)Time elapsed: 0.208 s
% 1.62/0.63  % (15307)------------------------------
% 1.62/0.63  % (15307)------------------------------
% 1.62/0.64  % (15319)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.62/0.64  % (15299)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.62/0.64  % (15299)Refutation not found, incomplete strategy% (15299)------------------------------
% 1.62/0.64  % (15299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.64  % (15299)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.64  
% 1.62/0.64  % (15299)Memory used [KB]: 10618
% 1.62/0.64  % (15299)Time elapsed: 0.203 s
% 1.62/0.64  % (15299)------------------------------
% 1.62/0.64  % (15299)------------------------------
% 1.62/0.64  % (15311)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 2.64/0.74  % (15344)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.75/0.74  % (15347)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.75/0.74  % (15344)Refutation not found, incomplete strategy% (15344)------------------------------
% 2.75/0.74  % (15344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.75/0.74  % (15344)Termination reason: Refutation not found, incomplete strategy
% 2.75/0.74  
% 2.75/0.74  % (15344)Memory used [KB]: 6140
% 2.75/0.74  % (15344)Time elapsed: 0.108 s
% 2.75/0.74  % (15344)------------------------------
% 2.75/0.74  % (15344)------------------------------
% 2.75/0.75  % (15298)Refutation found. Thanks to Tanya!
% 2.75/0.75  % SZS status Theorem for theBenchmark
% 2.75/0.75  % SZS output start Proof for theBenchmark
% 2.75/0.75  fof(f892,plain,(
% 2.75/0.75    $false),
% 2.75/0.75    inference(subsumption_resolution,[],[f891,f39])).
% 2.75/0.75  fof(f39,plain,(
% 2.75/0.75    sK0 != sK1),
% 2.75/0.75    inference(cnf_transformation,[],[f32])).
% 2.75/0.75  fof(f32,plain,(
% 2.75/0.75    sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 2.75/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f31])).
% 2.75/0.75  fof(f31,plain,(
% 2.75/0.75    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 2.75/0.75    introduced(choice_axiom,[])).
% 2.75/0.75  fof(f27,plain,(
% 2.75/0.75    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 2.75/0.75    inference(ennf_transformation,[],[f23])).
% 2.75/0.75  fof(f23,negated_conjecture,(
% 2.75/0.75    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.75/0.75    inference(negated_conjecture,[],[f22])).
% 2.75/0.75  fof(f22,conjecture,(
% 2.75/0.75    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 2.75/0.75  fof(f891,plain,(
% 2.75/0.75    sK0 = sK1),
% 2.75/0.75    inference(resolution,[],[f874,f94])).
% 2.75/0.75  fof(f94,plain,(
% 2.75/0.75    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 2.75/0.75    inference(equality_resolution,[],[f93])).
% 2.75/0.75  fof(f93,plain,(
% 2.75/0.75    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 2.75/0.75    inference(equality_resolution,[],[f87])).
% 2.75/0.75  fof(f87,plain,(
% 2.75/0.75    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.75/0.75    inference(definition_unfolding,[],[f58,f72])).
% 2.75/0.75  fof(f72,plain,(
% 2.75/0.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.75/0.75    inference(definition_unfolding,[],[f53,f71])).
% 2.75/0.75  fof(f71,plain,(
% 2.75/0.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.75/0.75    inference(definition_unfolding,[],[f55,f70])).
% 2.75/0.75  fof(f70,plain,(
% 2.75/0.75    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.75/0.75    inference(definition_unfolding,[],[f65,f69])).
% 2.75/0.75  fof(f69,plain,(
% 2.75/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.75/0.75    inference(definition_unfolding,[],[f66,f67])).
% 2.75/0.75  fof(f67,plain,(
% 2.75/0.75    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.75/0.75    inference(cnf_transformation,[],[f21])).
% 2.75/0.75  fof(f21,axiom,(
% 2.75/0.75    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.75/0.75  fof(f66,plain,(
% 2.75/0.75    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.75/0.75    inference(cnf_transformation,[],[f20])).
% 2.75/0.75  fof(f20,axiom,(
% 2.75/0.75    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.75/0.75  fof(f65,plain,(
% 2.75/0.75    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.75/0.75    inference(cnf_transformation,[],[f19])).
% 2.75/0.75  fof(f19,axiom,(
% 2.75/0.75    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.75/0.75  fof(f55,plain,(
% 2.75/0.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.75/0.75    inference(cnf_transformation,[],[f18])).
% 2.75/0.75  fof(f18,axiom,(
% 2.75/0.75    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.75/0.75  fof(f53,plain,(
% 2.75/0.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.75/0.75    inference(cnf_transformation,[],[f17])).
% 2.75/0.75  fof(f17,axiom,(
% 2.75/0.75    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.75/0.75  fof(f58,plain,(
% 2.75/0.75    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.75/0.75    inference(cnf_transformation,[],[f37])).
% 2.75/0.75  fof(f37,plain,(
% 2.75/0.75    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.75/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 2.75/0.75  fof(f36,plain,(
% 2.75/0.75    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 2.75/0.75    introduced(choice_axiom,[])).
% 2.75/0.75  fof(f35,plain,(
% 2.75/0.75    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.75/0.75    inference(rectify,[],[f34])).
% 2.75/0.75  fof(f34,plain,(
% 2.75/0.75    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.75/0.75    inference(flattening,[],[f33])).
% 2.75/0.75  fof(f33,plain,(
% 2.75/0.75    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.75/0.75    inference(nnf_transformation,[],[f30])).
% 2.75/0.75  fof(f30,plain,(
% 2.75/0.75    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.75/0.75    inference(ennf_transformation,[],[f12])).
% 2.75/0.75  fof(f12,axiom,(
% 2.75/0.75    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 2.75/0.75  fof(f874,plain,(
% 2.75/0.75    ( ! [X5] : (~r2_hidden(X5,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) | sK1 = X5) )),
% 2.75/0.75    inference(duplicate_literal_removal,[],[f873])).
% 2.75/0.75  fof(f873,plain,(
% 2.75/0.75    ( ! [X5] : (~r2_hidden(X5,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) | sK1 = X5 | sK1 = X5 | sK1 = X5) )),
% 2.75/0.75    inference(superposition,[],[f95,f802])).
% 2.75/0.75  fof(f802,plain,(
% 2.75/0.75    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),
% 2.75/0.75    inference(forward_demodulation,[],[f801,f100])).
% 2.75/0.75  fof(f100,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),
% 2.75/0.75    inference(forward_demodulation,[],[f97,f79])).
% 2.75/0.75  fof(f79,plain,(
% 2.75/0.75    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X0)) )),
% 2.75/0.75    inference(definition_unfolding,[],[f52,f72,f72])).
% 2.75/0.75  fof(f52,plain,(
% 2.75/0.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 2.75/0.75    inference(cnf_transformation,[],[f13])).
% 2.75/0.75  fof(f13,axiom,(
% 2.75/0.75    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).
% 2.75/0.75  fof(f97,plain,(
% 2.75/0.75    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.75/0.75    inference(superposition,[],[f80,f96])).
% 2.75/0.75  fof(f96,plain,(
% 2.75/0.75    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.75/0.75    inference(resolution,[],[f75,f50])).
% 2.75/0.75  fof(f50,plain,(
% 2.75/0.75    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.75/0.75    inference(cnf_transformation,[],[f28])).
% 2.75/0.75  fof(f28,plain,(
% 2.75/0.75    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.75/0.75    inference(ennf_transformation,[],[f7])).
% 2.75/0.75  fof(f7,axiom,(
% 2.75/0.75    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.75/0.75  fof(f75,plain,(
% 2.75/0.75    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.75/0.75    inference(definition_unfolding,[],[f38,f74,f74])).
% 2.75/0.75  fof(f74,plain,(
% 2.75/0.75    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.75/0.75    inference(definition_unfolding,[],[f41,f73])).
% 2.75/0.75  fof(f73,plain,(
% 2.75/0.75    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.75/0.75    inference(definition_unfolding,[],[f47,f72])).
% 2.75/0.75  fof(f47,plain,(
% 2.75/0.75    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.75/0.75    inference(cnf_transformation,[],[f16])).
% 2.75/0.75  fof(f16,axiom,(
% 2.75/0.75    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.75/0.75  fof(f41,plain,(
% 2.75/0.75    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.75/0.75    inference(cnf_transformation,[],[f15])).
% 2.75/0.75  fof(f15,axiom,(
% 2.75/0.75    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.75/0.75  fof(f38,plain,(
% 2.75/0.75    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 2.75/0.75    inference(cnf_transformation,[],[f32])).
% 2.75/0.75  fof(f80,plain,(
% 2.75/0.75    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k3_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))))) )),
% 2.75/0.75    inference(definition_unfolding,[],[f56,f71,f68,f72,f74])).
% 2.75/0.75  fof(f68,plain,(
% 2.75/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.75/0.75    inference(definition_unfolding,[],[f49,f48])).
% 2.75/0.75  fof(f48,plain,(
% 2.75/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.75/0.75    inference(cnf_transformation,[],[f5])).
% 2.75/0.75  fof(f5,axiom,(
% 2.75/0.75    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.75/0.75  fof(f49,plain,(
% 2.75/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.75/0.75    inference(cnf_transformation,[],[f11])).
% 2.75/0.75  fof(f11,axiom,(
% 2.75/0.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.75/0.75  fof(f56,plain,(
% 2.75/0.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 2.75/0.75    inference(cnf_transformation,[],[f14])).
% 2.75/0.75  fof(f14,axiom,(
% 2.75/0.75    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 2.75/0.75  fof(f801,plain,(
% 2.75/0.75    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.75/0.75    inference(forward_demodulation,[],[f796,f40])).
% 2.75/0.75  fof(f40,plain,(
% 2.75/0.75    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.75/0.75    inference(cnf_transformation,[],[f8])).
% 2.75/0.75  fof(f8,axiom,(
% 2.75/0.75    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.75/0.75  fof(f796,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)),
% 2.75/0.75    inference(superposition,[],[f706,f672])).
% 2.75/0.75  fof(f672,plain,(
% 2.75/0.75    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.75/0.75    inference(forward_demodulation,[],[f671,f475])).
% 2.75/0.75  fof(f475,plain,(
% 2.75/0.75    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.75/0.75    inference(forward_demodulation,[],[f473,f128])).
% 2.75/0.75  fof(f128,plain,(
% 2.75/0.75    k1_xboole_0 = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))),
% 2.75/0.75    inference(resolution,[],[f117,f51])).
% 2.75/0.75  fof(f51,plain,(
% 2.75/0.75    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.75/0.75    inference(cnf_transformation,[],[f29])).
% 2.75/0.75  fof(f29,plain,(
% 2.75/0.75    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 2.75/0.75    inference(ennf_transformation,[],[f26])).
% 2.75/0.75  fof(f26,plain,(
% 2.75/0.75    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.75/0.75    inference(unused_predicate_definition_removal,[],[f2])).
% 2.75/0.75  fof(f2,axiom,(
% 2.75/0.75    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.75/0.75  fof(f117,plain,(
% 2.75/0.75    r1_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))),
% 2.75/0.75    inference(superposition,[],[f77,f110])).
% 2.75/0.75  fof(f110,plain,(
% 2.75/0.75    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))),
% 2.75/0.75    inference(forward_demodulation,[],[f106,f105])).
% 2.75/0.75  fof(f105,plain,(
% 2.75/0.75    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 2.75/0.75    inference(superposition,[],[f80,f101])).
% 2.75/0.75  fof(f101,plain,(
% 2.75/0.75    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.75/0.75    inference(forward_demodulation,[],[f98,f100])).
% 2.75/0.75  fof(f98,plain,(
% 2.75/0.75    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 2.75/0.75    inference(superposition,[],[f78,f96])).
% 2.75/0.75  fof(f78,plain,(
% 2.75/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 2.75/0.75    inference(definition_unfolding,[],[f46,f68])).
% 2.75/0.75  fof(f46,plain,(
% 2.75/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.75/0.75    inference(cnf_transformation,[],[f6])).
% 2.75/0.75  fof(f6,axiom,(
% 2.75/0.75    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 2.75/0.75  fof(f106,plain,(
% 2.75/0.75    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 2.75/0.75    inference(superposition,[],[f78,f101])).
% 2.75/0.75  fof(f77,plain,(
% 2.75/0.75    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 2.75/0.75    inference(definition_unfolding,[],[f44,f48])).
% 2.75/0.75  fof(f44,plain,(
% 2.75/0.75    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.75/0.75    inference(cnf_transformation,[],[f9])).
% 2.75/0.75  fof(f9,axiom,(
% 2.75/0.75    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.75/0.75  fof(f473,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))),
% 2.75/0.75    inference(backward_demodulation,[],[f214,f471])).
% 2.75/0.75  fof(f471,plain,(
% 2.75/0.75    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))),
% 2.75/0.75    inference(forward_demodulation,[],[f470,f362])).
% 2.75/0.75  fof(f362,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))),
% 2.75/0.75    inference(superposition,[],[f263,f105])).
% 2.75/0.75  fof(f263,plain,(
% 2.75/0.75    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),X0))) )),
% 2.75/0.75    inference(superposition,[],[f222,f115])).
% 2.75/0.75  fof(f115,plain,(
% 2.75/0.75    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),X0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)))) )),
% 2.75/0.75    inference(forward_demodulation,[],[f114,f54])).
% 2.75/0.75  fof(f54,plain,(
% 2.75/0.75    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.75/0.75    inference(cnf_transformation,[],[f10])).
% 2.75/0.75  fof(f10,axiom,(
% 2.75/0.75    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.75/0.75  fof(f114,plain,(
% 2.75/0.75    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),X0)) )),
% 2.75/0.75    inference(superposition,[],[f54,f100])).
% 2.75/0.75  fof(f222,plain,(
% 2.75/0.75    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) )),
% 2.75/0.75    inference(forward_demodulation,[],[f221,f54])).
% 2.75/0.75  fof(f221,plain,(
% 2.75/0.75    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) )),
% 2.75/0.75    inference(superposition,[],[f54,f193])).
% 2.75/0.75  fof(f193,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.75/0.75    inference(forward_demodulation,[],[f189,f43])).
% 2.75/0.75  fof(f43,plain,(
% 2.75/0.75    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.75/0.75    inference(cnf_transformation,[],[f25])).
% 2.75/0.75  fof(f25,plain,(
% 2.75/0.75    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.75/0.75    inference(rectify,[],[f4])).
% 2.75/0.75  fof(f4,axiom,(
% 2.75/0.75    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.75/0.75  fof(f189,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 2.75/0.75    inference(superposition,[],[f139,f80])).
% 2.75/0.75  fof(f139,plain,(
% 2.75/0.75    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)))) )),
% 2.75/0.75    inference(forward_demodulation,[],[f138,f54])).
% 2.75/0.75  fof(f138,plain,(
% 2.75/0.75    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),X0)) )),
% 2.75/0.75    inference(superposition,[],[f54,f105])).
% 2.75/0.75  fof(f470,plain,(
% 2.75/0.75    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))),
% 2.75/0.75    inference(forward_demodulation,[],[f466,f43])).
% 2.75/0.75  fof(f466,plain,(
% 2.75/0.75    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))))),
% 2.75/0.75    inference(superposition,[],[f363,f76])).
% 2.75/0.75  fof(f76,plain,(
% 2.75/0.75    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 2.75/0.75    inference(definition_unfolding,[],[f42,f68])).
% 2.75/0.75  fof(f42,plain,(
% 2.75/0.75    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.75/0.75    inference(cnf_transformation,[],[f24])).
% 2.75/0.75  fof(f24,plain,(
% 2.75/0.75    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.75/0.75    inference(rectify,[],[f3])).
% 2.75/0.75  fof(f3,axiom,(
% 2.75/0.75    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.75/0.75  fof(f363,plain,(
% 2.75/0.75    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),X0))) )),
% 2.75/0.75    inference(superposition,[],[f263,f139])).
% 2.75/0.75  fof(f214,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))))),
% 2.75/0.75    inference(forward_demodulation,[],[f213,f40])).
% 2.75/0.75  fof(f213,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k1_xboole_0))))),
% 2.75/0.75    inference(forward_demodulation,[],[f211,f54])).
% 2.75/0.75  fof(f211,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k1_xboole_0)))),
% 2.75/0.75    inference(superposition,[],[f78,f166])).
% 2.75/0.75  fof(f166,plain,(
% 2.75/0.75    k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)))),
% 2.75/0.75    inference(superposition,[],[f128,f45])).
% 2.75/0.75  fof(f45,plain,(
% 2.75/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.75/0.75    inference(cnf_transformation,[],[f1])).
% 2.75/0.75  fof(f1,axiom,(
% 2.75/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.75/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.75/0.75  fof(f671,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.75/0.75    inference(forward_demodulation,[],[f649,f311])).
% 2.75/0.75  fof(f311,plain,(
% 2.75/0.75    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0,X1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0,X1))) )),
% 2.75/0.75    inference(superposition,[],[f253,f80])).
% 2.75/0.75  fof(f253,plain,(
% 2.75/0.75    ( ! [X2,X1] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1),X2)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1),X2))) )),
% 2.75/0.75    inference(forward_demodulation,[],[f252,f54])).
% 2.75/0.75  fof(f252,plain,(
% 2.75/0.75    ( ! [X2,X1] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1),X2)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),X2)) )),
% 2.75/0.75    inference(superposition,[],[f54,f223])).
% 2.75/0.75  fof(f223,plain,(
% 2.75/0.75    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0))) )),
% 2.75/0.75    inference(superposition,[],[f175,f80])).
% 2.75/0.75  fof(f175,plain,(
% 2.75/0.75    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) )),
% 2.75/0.75    inference(forward_demodulation,[],[f174,f54])).
% 2.75/0.75  fof(f174,plain,(
% 2.75/0.75    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) )),
% 2.75/0.75    inference(superposition,[],[f54,f153])).
% 2.75/0.75  fof(f153,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.75/0.75    inference(forward_demodulation,[],[f149,f43])).
% 2.75/0.75  fof(f149,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.75/0.75    inference(superposition,[],[f115,f80])).
% 2.75/0.75  fof(f649,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.75/0.75    inference(superposition,[],[f620,f100])).
% 2.75/0.75  fof(f620,plain,(
% 2.75/0.75    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 2.75/0.75    inference(superposition,[],[f54,f490])).
% 2.75/0.75  fof(f490,plain,(
% 2.75/0.75    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.75/0.75    inference(forward_demodulation,[],[f489,f113])).
% 2.75/0.75  fof(f113,plain,(
% 2.75/0.75    k1_xboole_0 = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.75/0.75    inference(resolution,[],[f109,f51])).
% 2.75/0.75  fof(f109,plain,(
% 2.75/0.75    r1_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.75/0.75    inference(superposition,[],[f77,f101])).
% 2.75/0.75  fof(f489,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.75/0.75    inference(forward_demodulation,[],[f483,f40])).
% 2.75/0.75  fof(f483,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k1_xboole_0))),
% 2.75/0.75    inference(backward_demodulation,[],[f346,f475])).
% 2.75/0.75  fof(f346,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))))),
% 2.75/0.75    inference(backward_demodulation,[],[f325,f337])).
% 2.75/0.75  fof(f337,plain,(
% 2.75/0.75    ( ! [X6,X7,X5] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X5,X6),X7)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X5,X6),X7))) )),
% 2.75/0.75    inference(forward_demodulation,[],[f336,f54])).
% 2.75/0.75  fof(f336,plain,(
% 2.75/0.75    ( ! [X6,X7,X5] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X5,X6),X7)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X5,X6)),X7)) )),
% 2.75/0.75    inference(superposition,[],[f54,f311])).
% 2.75/0.75  fof(f325,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))))),
% 2.75/0.75    inference(backward_demodulation,[],[f180,f311])).
% 2.75/0.75  fof(f180,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))))),
% 2.75/0.75    inference(forward_demodulation,[],[f179,f40])).
% 2.75/0.75  fof(f179,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k1_xboole_0))))),
% 2.75/0.75    inference(forward_demodulation,[],[f177,f54])).
% 2.75/0.75  fof(f177,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k1_xboole_0)))),
% 2.75/0.75    inference(superposition,[],[f78,f129])).
% 2.75/0.75  fof(f129,plain,(
% 2.75/0.75    k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 2.75/0.75    inference(superposition,[],[f113,f45])).
% 2.75/0.75  fof(f706,plain,(
% 2.75/0.75    ( ! [X6] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X6) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,X6))) )),
% 2.75/0.75    inference(backward_demodulation,[],[f654,f705])).
% 2.75/0.75  fof(f705,plain,(
% 2.75/0.75    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) )),
% 2.75/0.75    inference(superposition,[],[f54,f675])).
% 2.75/0.75  fof(f675,plain,(
% 2.75/0.75    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.75/0.75    inference(forward_demodulation,[],[f662,f40])).
% 2.75/0.75  fof(f662,plain,(
% 2.75/0.75    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.75/0.75    inference(superposition,[],[f620,f490])).
% 2.75/0.75  fof(f654,plain,(
% 2.75/0.75    ( ! [X6] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X6)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,X6))) )),
% 2.75/0.75    inference(superposition,[],[f620,f620])).
% 2.75/0.75  fof(f95,plain,(
% 2.75/0.75    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 2.75/0.75    inference(equality_resolution,[],[f88])).
% 2.75/0.75  fof(f88,plain,(
% 2.75/0.75    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.75/0.75    inference(definition_unfolding,[],[f57,f72])).
% 2.75/0.75  fof(f57,plain,(
% 2.75/0.75    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.75/0.75    inference(cnf_transformation,[],[f37])).
% 2.75/0.75  % SZS output end Proof for theBenchmark
% 2.75/0.75  % (15298)------------------------------
% 2.75/0.75  % (15298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.75/0.75  % (15298)Termination reason: Refutation
% 2.75/0.75  
% 2.75/0.75  % (15298)Memory used [KB]: 11641
% 2.75/0.75  % (15298)Time elapsed: 0.322 s
% 2.75/0.75  % (15298)------------------------------
% 2.75/0.75  % (15298)------------------------------
% 2.75/0.75  % (15289)Success in time 0.384 s
%------------------------------------------------------------------------------
