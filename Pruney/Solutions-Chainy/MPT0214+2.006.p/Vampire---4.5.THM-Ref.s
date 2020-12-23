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
% DateTime   : Thu Dec  3 12:34:58 EST 2020

% Result     : Theorem 2.16s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  147 (23320 expanded)
%              Number of leaves         :   24 (7916 expanded)
%              Depth                    :   42
%              Number of atoms          :  272 (25027 expanded)
%              Number of equality atoms :  220 (23240 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1032,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1031,f39])).

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

fof(f1031,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f1012,f94])).

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

fof(f1012,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))
      | sK1 = X5 ) ),
    inference(duplicate_literal_removal,[],[f1011])).

fof(f1011,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))
      | sK1 = X5
      | sK1 = X5
      | sK1 = X5 ) ),
    inference(superposition,[],[f95,f932])).

fof(f932,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) ),
    inference(forward_demodulation,[],[f931,f101])).

fof(f101,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) ),
    inference(forward_demodulation,[],[f100,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f52,f72,f72])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(f100,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0,sK1) ),
    inference(forward_demodulation,[],[f97,f79])).

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

fof(f931,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f926,f40])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f926,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) ),
    inference(superposition,[],[f808,f773])).

fof(f773,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f772,f560])).

fof(f560,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(forward_demodulation,[],[f558,f129])).

fof(f129,plain,(
    k1_xboole_0 = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) ),
    inference(resolution,[],[f118,f51])).

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

fof(f118,plain,(
    r1_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) ),
    inference(superposition,[],[f77,f111])).

fof(f111,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f107,f106])).

fof(f106,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f80,f102])).

fof(f102,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(forward_demodulation,[],[f98,f101])).

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

fof(f107,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f78,f102])).

fof(f77,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f44,f48])).

fof(f44,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f558,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) ),
    inference(backward_demodulation,[],[f215,f556])).

fof(f556,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f555,f384])).

fof(f384,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) ),
    inference(superposition,[],[f270,f106])).

fof(f270,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),X0)) ),
    inference(superposition,[],[f223,f116])).

fof(f116,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),X0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) ),
    inference(forward_demodulation,[],[f115,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f115,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),X0) ),
    inference(superposition,[],[f54,f101])).

fof(f223,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) ),
    inference(forward_demodulation,[],[f222,f54])).

fof(f222,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0) ),
    inference(superposition,[],[f54,f194])).

fof(f194,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f190,f43])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f190,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f140,f80])).

fof(f140,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) ),
    inference(forward_demodulation,[],[f139,f54])).

fof(f139,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),X0) ),
    inference(superposition,[],[f54,f106])).

fof(f555,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f551,f43])).

fof(f551,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f385,f76])).

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

fof(f385,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),X0)) ),
    inference(superposition,[],[f270,f140])).

fof(f215,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f214,f40])).

fof(f214,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f212,f54])).

fof(f212,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k1_xboole_0))) ),
    inference(superposition,[],[f78,f167])).

fof(f167,plain,(
    k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))) ),
    inference(superposition,[],[f129,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f772,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f746,f324])).

fof(f324,plain,(
    ! [X0,X1] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0,X1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0,X1)) ),
    inference(superposition,[],[f254,f80])).

fof(f254,plain,(
    ! [X2,X1] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1),X2)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1),X2)) ),
    inference(forward_demodulation,[],[f253,f54])).

fof(f253,plain,(
    ! [X2,X1] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1),X2)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),X2) ),
    inference(superposition,[],[f54,f224])).

fof(f224,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)) ),
    inference(superposition,[],[f176,f80])).

fof(f176,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) ),
    inference(forward_demodulation,[],[f175,f54])).

fof(f175,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0) ),
    inference(superposition,[],[f54,f154])).

fof(f154,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f150,f43])).

fof(f150,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f116,f80])).

fof(f746,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f717,f101])).

fof(f717,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f54,f575])).

fof(f575,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f574,f114])).

fof(f114,plain,(
    k1_xboole_0 = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(resolution,[],[f110,f51])).

fof(f110,plain,(
    r1_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(superposition,[],[f77,f102])).

fof(f574,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) ),
    inference(forward_demodulation,[],[f568,f40])).

fof(f568,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f361,f560])).

fof(f361,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)))) ),
    inference(backward_demodulation,[],[f338,f350])).

fof(f350,plain,(
    ! [X6,X8,X7] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X6,X7),X8)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X6,X7),X8)) ),
    inference(forward_demodulation,[],[f349,f54])).

fof(f349,plain,(
    ! [X6,X8,X7] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X6,X7),X8)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X6,X7)),X8) ),
    inference(superposition,[],[f54,f324])).

fof(f338,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)))) ),
    inference(backward_demodulation,[],[f181,f324])).

fof(f181,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f180,f40])).

fof(f180,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f178,f54])).

fof(f178,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k1_xboole_0))) ),
    inference(superposition,[],[f78,f130])).

fof(f130,plain,(
    k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[],[f114,f45])).

fof(f808,plain,(
    ! [X8] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X8) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,X8)) ),
    inference(backward_demodulation,[],[f752,f807])).

fof(f807,plain,(
    ! [X0] : k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) ),
    inference(superposition,[],[f54,f776])).

fof(f776,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f763,f40])).

fof(f763,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f717,f575])).

fof(f752,plain,(
    ! [X8] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X8)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,X8)) ),
    inference(superposition,[],[f717,f717])).

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
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:08:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (30528)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.47  % (30528)Refutation not found, incomplete strategy% (30528)------------------------------
% 0.20/0.47  % (30528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (30528)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (30528)Memory used [KB]: 10618
% 0.20/0.47  % (30528)Time elapsed: 0.063 s
% 0.20/0.47  % (30528)------------------------------
% 0.20/0.47  % (30528)------------------------------
% 0.20/0.48  % (30536)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.48  % (30536)Refutation not found, incomplete strategy% (30536)------------------------------
% 0.20/0.48  % (30536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (30536)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (30536)Memory used [KB]: 10618
% 0.20/0.48  % (30536)Time elapsed: 0.075 s
% 0.20/0.48  % (30536)------------------------------
% 0.20/0.48  % (30536)------------------------------
% 0.20/0.51  % (30523)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (30541)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (30533)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (30520)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (30547)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (30527)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (30519)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (30519)Refutation not found, incomplete strategy% (30519)------------------------------
% 0.20/0.53  % (30519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (30519)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (30519)Memory used [KB]: 1663
% 0.20/0.53  % (30519)Time elapsed: 0.121 s
% 0.20/0.53  % (30519)------------------------------
% 0.20/0.53  % (30519)------------------------------
% 0.20/0.53  % (30548)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (30546)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (30545)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (30544)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (30524)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (30521)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (30543)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (30526)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (30530)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (30539)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (30534)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (30540)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (30535)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (30537)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (30538)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (30534)Refutation not found, incomplete strategy% (30534)------------------------------
% 0.20/0.55  % (30534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (30534)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (30534)Memory used [KB]: 6140
% 0.20/0.55  % (30534)Time elapsed: 0.137 s
% 0.20/0.55  % (30534)------------------------------
% 0.20/0.55  % (30534)------------------------------
% 0.20/0.55  % (30542)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (30522)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.55  % (30531)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (30532)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (30529)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (30525)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.55  % (30529)Refutation not found, incomplete strategy% (30529)------------------------------
% 0.20/0.55  % (30529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (30529)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (30529)Memory used [KB]: 10618
% 0.20/0.55  % (30529)Time elapsed: 0.147 s
% 0.20/0.55  % (30529)------------------------------
% 0.20/0.55  % (30529)------------------------------
% 0.20/0.56  % (30530)Refutation not found, incomplete strategy% (30530)------------------------------
% 0.20/0.56  % (30530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (30530)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (30530)Memory used [KB]: 10618
% 0.20/0.56  % (30530)Time elapsed: 0.156 s
% 0.20/0.56  % (30530)------------------------------
% 0.20/0.56  % (30530)------------------------------
% 1.64/0.58  % (30549)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.80/0.58  % (30549)Refutation not found, incomplete strategy% (30549)------------------------------
% 1.80/0.58  % (30549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.58  % (30549)Termination reason: Refutation not found, incomplete strategy
% 1.80/0.58  
% 1.80/0.58  % (30549)Memory used [KB]: 6140
% 1.80/0.58  % (30549)Time elapsed: 0.005 s
% 1.80/0.58  % (30549)------------------------------
% 1.80/0.58  % (30549)------------------------------
% 1.80/0.59  % (30550)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.16/0.67  % (30520)Refutation not found, incomplete strategy% (30520)------------------------------
% 2.16/0.67  % (30520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.68  % (30551)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.16/0.68  % (30552)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.16/0.68  % (30527)Refutation found. Thanks to Tanya!
% 2.16/0.68  % SZS status Theorem for theBenchmark
% 2.16/0.68  % SZS output start Proof for theBenchmark
% 2.16/0.68  fof(f1032,plain,(
% 2.16/0.68    $false),
% 2.16/0.68    inference(subsumption_resolution,[],[f1031,f39])).
% 2.16/0.68  fof(f39,plain,(
% 2.16/0.68    sK0 != sK1),
% 2.16/0.68    inference(cnf_transformation,[],[f32])).
% 2.16/0.68  fof(f32,plain,(
% 2.16/0.68    sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 2.16/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f31])).
% 2.16/0.68  fof(f31,plain,(
% 2.16/0.68    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 2.16/0.68    introduced(choice_axiom,[])).
% 2.16/0.68  fof(f27,plain,(
% 2.16/0.68    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 2.16/0.68    inference(ennf_transformation,[],[f23])).
% 2.16/0.68  fof(f23,negated_conjecture,(
% 2.16/0.68    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.16/0.68    inference(negated_conjecture,[],[f22])).
% 2.16/0.68  fof(f22,conjecture,(
% 2.16/0.68    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.16/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 2.16/0.68  fof(f1031,plain,(
% 2.16/0.68    sK0 = sK1),
% 2.16/0.68    inference(resolution,[],[f1012,f94])).
% 2.16/0.68  fof(f94,plain,(
% 2.16/0.68    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 2.16/0.68    inference(equality_resolution,[],[f93])).
% 2.16/0.68  fof(f93,plain,(
% 2.16/0.68    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 2.16/0.68    inference(equality_resolution,[],[f87])).
% 2.16/0.68  fof(f87,plain,(
% 2.16/0.68    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.16/0.68    inference(definition_unfolding,[],[f58,f72])).
% 2.16/0.68  fof(f72,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.16/0.68    inference(definition_unfolding,[],[f53,f71])).
% 2.16/0.68  fof(f71,plain,(
% 2.16/0.68    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.16/0.68    inference(definition_unfolding,[],[f55,f70])).
% 2.16/0.68  fof(f70,plain,(
% 2.16/0.68    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.16/0.68    inference(definition_unfolding,[],[f65,f69])).
% 2.16/0.68  fof(f69,plain,(
% 2.16/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.16/0.68    inference(definition_unfolding,[],[f66,f67])).
% 2.16/0.68  fof(f67,plain,(
% 2.16/0.68    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f21])).
% 2.16/0.68  fof(f21,axiom,(
% 2.16/0.68    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.16/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.16/0.68  fof(f66,plain,(
% 2.16/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f20])).
% 2.16/0.68  fof(f20,axiom,(
% 2.16/0.68    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.16/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.16/0.68  fof(f65,plain,(
% 2.16/0.68    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f19])).
% 2.16/0.68  fof(f19,axiom,(
% 2.16/0.68    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.16/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.16/0.68  fof(f55,plain,(
% 2.16/0.68    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f18])).
% 2.16/0.68  fof(f18,axiom,(
% 2.16/0.68    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.16/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.16/0.68  fof(f53,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f17])).
% 2.16/0.68  fof(f17,axiom,(
% 2.16/0.68    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.16/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.16/0.68  fof(f58,plain,(
% 2.16/0.68    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.16/0.68    inference(cnf_transformation,[],[f37])).
% 2.16/0.68  fof(f37,plain,(
% 2.16/0.68    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.16/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 2.16/0.68  fof(f36,plain,(
% 2.16/0.68    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 2.16/0.68    introduced(choice_axiom,[])).
% 2.16/0.68  fof(f35,plain,(
% 2.16/0.68    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.16/0.68    inference(rectify,[],[f34])).
% 2.16/0.68  fof(f34,plain,(
% 2.16/0.68    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.16/0.68    inference(flattening,[],[f33])).
% 2.16/0.68  fof(f33,plain,(
% 2.16/0.68    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.16/0.68    inference(nnf_transformation,[],[f30])).
% 2.16/0.68  fof(f30,plain,(
% 2.16/0.68    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.16/0.68    inference(ennf_transformation,[],[f12])).
% 2.16/0.68  fof(f12,axiom,(
% 2.16/0.68    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.16/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 2.16/0.68  fof(f1012,plain,(
% 2.16/0.68    ( ! [X5] : (~r2_hidden(X5,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) | sK1 = X5) )),
% 2.16/0.68    inference(duplicate_literal_removal,[],[f1011])).
% 2.16/0.68  fof(f1011,plain,(
% 2.16/0.68    ( ! [X5] : (~r2_hidden(X5,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) | sK1 = X5 | sK1 = X5 | sK1 = X5) )),
% 2.16/0.68    inference(superposition,[],[f95,f932])).
% 2.16/0.68  fof(f932,plain,(
% 2.16/0.68    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),
% 2.16/0.68    inference(forward_demodulation,[],[f931,f101])).
% 2.16/0.68  fof(f101,plain,(
% 2.16/0.68    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),
% 2.16/0.68    inference(forward_demodulation,[],[f100,f79])).
% 2.16/0.68  fof(f79,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) )),
% 2.16/0.68    inference(definition_unfolding,[],[f52,f72,f72])).
% 2.16/0.68  fof(f52,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f13])).
% 2.16/0.68  fof(f13,axiom,(
% 2.16/0.68    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 2.16/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).
% 2.16/0.68  fof(f100,plain,(
% 2.16/0.68    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0,sK1)),
% 2.16/0.68    inference(forward_demodulation,[],[f97,f79])).
% 2.16/0.68  fof(f97,plain,(
% 2.16/0.68    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.16/0.68    inference(superposition,[],[f80,f96])).
% 2.16/0.68  fof(f96,plain,(
% 2.16/0.68    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.16/0.68    inference(resolution,[],[f75,f50])).
% 2.16/0.68  fof(f50,plain,(
% 2.16/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.16/0.68    inference(cnf_transformation,[],[f28])).
% 2.16/0.68  fof(f28,plain,(
% 2.16/0.68    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.16/0.68    inference(ennf_transformation,[],[f7])).
% 2.16/0.68  fof(f7,axiom,(
% 2.16/0.68    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.16/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.16/0.68  fof(f75,plain,(
% 2.16/0.68    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.16/0.68    inference(definition_unfolding,[],[f38,f74,f74])).
% 2.16/0.68  fof(f74,plain,(
% 2.16/0.68    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.16/0.68    inference(definition_unfolding,[],[f41,f73])).
% 2.16/0.68  fof(f73,plain,(
% 2.16/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.16/0.68    inference(definition_unfolding,[],[f47,f72])).
% 2.16/0.68  fof(f47,plain,(
% 2.16/0.68    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f16])).
% 2.16/0.68  fof(f16,axiom,(
% 2.16/0.68    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.16/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.16/0.68  fof(f41,plain,(
% 2.16/0.68    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f15])).
% 2.16/0.68  fof(f15,axiom,(
% 2.16/0.68    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.16/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.16/0.68  fof(f38,plain,(
% 2.16/0.68    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 2.16/0.68    inference(cnf_transformation,[],[f32])).
% 2.16/0.68  fof(f80,plain,(
% 2.16/0.68    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k3_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))))) )),
% 2.16/0.68    inference(definition_unfolding,[],[f56,f71,f68,f72,f74])).
% 2.16/0.68  fof(f68,plain,(
% 2.16/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.16/0.68    inference(definition_unfolding,[],[f49,f48])).
% 2.16/0.68  fof(f48,plain,(
% 2.16/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.16/0.68    inference(cnf_transformation,[],[f5])).
% 2.16/0.68  fof(f5,axiom,(
% 2.16/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.16/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.16/0.68  fof(f49,plain,(
% 2.16/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.16/0.68    inference(cnf_transformation,[],[f11])).
% 2.16/0.68  fof(f11,axiom,(
% 2.16/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.16/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.16/0.68  fof(f56,plain,(
% 2.16/0.68    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 2.16/0.68    inference(cnf_transformation,[],[f14])).
% 2.16/0.68  fof(f14,axiom,(
% 2.16/0.68    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 2.16/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 2.16/0.68  fof(f931,plain,(
% 2.16/0.68    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.16/0.68    inference(forward_demodulation,[],[f926,f40])).
% 2.16/0.68  fof(f40,plain,(
% 2.16/0.68    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.16/0.68    inference(cnf_transformation,[],[f8])).
% 2.16/0.68  fof(f8,axiom,(
% 2.16/0.68    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.16/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.16/0.68  fof(f926,plain,(
% 2.16/0.68    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)),
% 2.16/0.68    inference(superposition,[],[f808,f773])).
% 2.16/0.68  fof(f773,plain,(
% 2.16/0.68    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.16/0.68    inference(forward_demodulation,[],[f772,f560])).
% 2.16/0.68  fof(f560,plain,(
% 2.16/0.68    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.16/0.68    inference(forward_demodulation,[],[f558,f129])).
% 2.16/0.68  fof(f129,plain,(
% 2.16/0.68    k1_xboole_0 = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))),
% 2.16/0.68    inference(resolution,[],[f118,f51])).
% 2.16/0.68  fof(f51,plain,(
% 2.16/0.68    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.16/0.68    inference(cnf_transformation,[],[f29])).
% 2.16/0.68  fof(f29,plain,(
% 2.16/0.68    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 2.16/0.68    inference(ennf_transformation,[],[f26])).
% 2.16/0.68  fof(f26,plain,(
% 2.16/0.68    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.16/0.68    inference(unused_predicate_definition_removal,[],[f2])).
% 2.16/0.68  fof(f2,axiom,(
% 2.16/0.68    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.16/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.16/0.68  fof(f118,plain,(
% 2.16/0.68    r1_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))),
% 2.16/0.68    inference(superposition,[],[f77,f111])).
% 2.16/0.68  fof(f111,plain,(
% 2.16/0.68    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))),
% 2.16/0.68    inference(forward_demodulation,[],[f107,f106])).
% 2.16/0.68  fof(f106,plain,(
% 2.16/0.68    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 2.16/0.68    inference(superposition,[],[f80,f102])).
% 2.16/0.68  fof(f102,plain,(
% 2.16/0.68    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.16/0.68    inference(forward_demodulation,[],[f98,f101])).
% 2.16/0.68  fof(f98,plain,(
% 2.16/0.68    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 2.16/0.68    inference(superposition,[],[f78,f96])).
% 2.16/0.68  fof(f78,plain,(
% 2.16/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 2.16/0.68    inference(definition_unfolding,[],[f46,f68])).
% 2.16/0.68  fof(f46,plain,(
% 2.16/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.16/0.68    inference(cnf_transformation,[],[f6])).
% 2.16/0.68  fof(f6,axiom,(
% 2.16/0.68    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.16/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 2.16/0.68  fof(f107,plain,(
% 2.16/0.68    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 2.16/0.68    inference(superposition,[],[f78,f102])).
% 2.16/0.68  fof(f77,plain,(
% 2.16/0.68    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 2.16/0.68    inference(definition_unfolding,[],[f44,f48])).
% 2.16/0.68  fof(f44,plain,(
% 2.16/0.68    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.16/0.68    inference(cnf_transformation,[],[f9])).
% 2.16/0.68  fof(f9,axiom,(
% 2.16/0.68    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.16/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.16/0.68  fof(f558,plain,(
% 2.16/0.68    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))),
% 2.16/0.68    inference(backward_demodulation,[],[f215,f556])).
% 2.16/0.68  fof(f556,plain,(
% 2.16/0.68    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))),
% 2.16/0.68    inference(forward_demodulation,[],[f555,f384])).
% 2.16/0.68  fof(f384,plain,(
% 2.16/0.68    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))),
% 2.16/0.68    inference(superposition,[],[f270,f106])).
% 2.16/0.68  fof(f270,plain,(
% 2.16/0.68    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),X0))) )),
% 2.16/0.68    inference(superposition,[],[f223,f116])).
% 2.16/0.68  fof(f116,plain,(
% 2.16/0.68    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),X0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)))) )),
% 2.16/0.68    inference(forward_demodulation,[],[f115,f54])).
% 2.16/0.68  fof(f54,plain,(
% 2.16/0.68    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.16/0.68    inference(cnf_transformation,[],[f10])).
% 2.16/0.68  fof(f10,axiom,(
% 2.16/0.68    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.16/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.16/0.68  fof(f115,plain,(
% 2.16/0.68    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),X0)) )),
% 2.16/0.68    inference(superposition,[],[f54,f101])).
% 2.16/0.68  fof(f223,plain,(
% 2.16/0.68    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) )),
% 2.16/0.68    inference(forward_demodulation,[],[f222,f54])).
% 2.16/0.68  fof(f222,plain,(
% 2.16/0.68    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) )),
% 2.16/0.68    inference(superposition,[],[f54,f194])).
% 2.16/0.68  fof(f194,plain,(
% 2.16/0.68    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.16/0.68    inference(forward_demodulation,[],[f190,f43])).
% 2.16/0.68  fof(f43,plain,(
% 2.16/0.68    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.16/0.68    inference(cnf_transformation,[],[f25])).
% 2.16/0.68  fof(f25,plain,(
% 2.16/0.68    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.16/0.68    inference(rectify,[],[f4])).
% 2.16/0.68  fof(f4,axiom,(
% 2.16/0.68    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.16/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.16/0.68  fof(f190,plain,(
% 2.16/0.68    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 2.16/0.68    inference(superposition,[],[f140,f80])).
% 2.16/0.68  fof(f140,plain,(
% 2.16/0.68    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)))) )),
% 2.16/0.68    inference(forward_demodulation,[],[f139,f54])).
% 2.16/0.68  fof(f139,plain,(
% 2.16/0.68    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),X0)) )),
% 2.16/0.68    inference(superposition,[],[f54,f106])).
% 2.16/0.68  fof(f555,plain,(
% 2.16/0.68    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))),
% 2.16/0.68    inference(forward_demodulation,[],[f551,f43])).
% 2.16/0.68  fof(f551,plain,(
% 2.16/0.68    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))))),
% 2.16/0.68    inference(superposition,[],[f385,f76])).
% 2.16/0.68  fof(f76,plain,(
% 2.16/0.68    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 2.16/0.68    inference(definition_unfolding,[],[f42,f68])).
% 2.16/0.69  fof(f42,plain,(
% 2.16/0.69    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.16/0.69    inference(cnf_transformation,[],[f24])).
% 2.16/0.69  fof(f24,plain,(
% 2.16/0.69    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.16/0.69    inference(rectify,[],[f3])).
% 2.16/0.69  fof(f3,axiom,(
% 2.16/0.69    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.16/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.16/0.69  fof(f385,plain,(
% 2.16/0.69    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),X0))) )),
% 2.16/0.69    inference(superposition,[],[f270,f140])).
% 2.16/0.69  fof(f215,plain,(
% 2.16/0.69    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))))),
% 2.16/0.69    inference(forward_demodulation,[],[f214,f40])).
% 2.16/0.69  fof(f214,plain,(
% 2.16/0.69    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k1_xboole_0))))),
% 2.16/0.69    inference(forward_demodulation,[],[f212,f54])).
% 2.16/0.69  fof(f212,plain,(
% 2.16/0.69    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k1_xboole_0)))),
% 2.16/0.69    inference(superposition,[],[f78,f167])).
% 2.16/0.69  fof(f167,plain,(
% 2.16/0.69    k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)))),
% 2.16/0.69    inference(superposition,[],[f129,f45])).
% 2.16/0.69  fof(f45,plain,(
% 2.16/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.16/0.69    inference(cnf_transformation,[],[f1])).
% 2.16/0.69  fof(f1,axiom,(
% 2.16/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.16/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.16/0.69  fof(f772,plain,(
% 2.16/0.69    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.16/0.69    inference(forward_demodulation,[],[f746,f324])).
% 2.16/0.69  fof(f324,plain,(
% 2.16/0.69    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0,X1)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0,X1))) )),
% 2.16/0.69    inference(superposition,[],[f254,f80])).
% 2.16/0.69  fof(f254,plain,(
% 2.16/0.69    ( ! [X2,X1] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1),X2)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1),X2))) )),
% 2.16/0.69    inference(forward_demodulation,[],[f253,f54])).
% 2.16/0.69  fof(f253,plain,(
% 2.16/0.69    ( ! [X2,X1] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1),X2)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X1)),X2)) )),
% 2.16/0.69    inference(superposition,[],[f54,f224])).
% 2.16/0.69  fof(f224,plain,(
% 2.16/0.69    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0))) )),
% 2.16/0.69    inference(superposition,[],[f176,f80])).
% 2.16/0.69  fof(f176,plain,(
% 2.16/0.69    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) )),
% 2.16/0.69    inference(forward_demodulation,[],[f175,f54])).
% 2.16/0.69  fof(f175,plain,(
% 2.16/0.69    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) )),
% 2.16/0.69    inference(superposition,[],[f54,f154])).
% 2.16/0.69  fof(f154,plain,(
% 2.16/0.69    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.16/0.69    inference(forward_demodulation,[],[f150,f43])).
% 2.16/0.69  fof(f150,plain,(
% 2.16/0.69    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.16/0.69    inference(superposition,[],[f116,f80])).
% 2.16/0.69  fof(f746,plain,(
% 2.16/0.69    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.16/0.69    inference(superposition,[],[f717,f101])).
% 2.16/0.69  fof(f717,plain,(
% 2.16/0.69    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 2.16/0.69    inference(superposition,[],[f54,f575])).
% 2.16/0.69  fof(f575,plain,(
% 2.16/0.69    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.16/0.69    inference(forward_demodulation,[],[f574,f114])).
% 2.16/0.69  fof(f114,plain,(
% 2.16/0.69    k1_xboole_0 = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.16/0.69    inference(resolution,[],[f110,f51])).
% 2.16/0.69  fof(f110,plain,(
% 2.16/0.69    r1_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.16/0.69    inference(superposition,[],[f77,f102])).
% 2.16/0.69  fof(f574,plain,(
% 2.16/0.69    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))),
% 2.16/0.69    inference(forward_demodulation,[],[f568,f40])).
% 2.16/0.69  fof(f568,plain,(
% 2.16/0.69    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k1_xboole_0))),
% 2.16/0.69    inference(backward_demodulation,[],[f361,f560])).
% 2.16/0.69  fof(f361,plain,(
% 2.16/0.69    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))))),
% 2.16/0.69    inference(backward_demodulation,[],[f338,f350])).
% 2.16/0.69  fof(f350,plain,(
% 2.16/0.69    ( ! [X6,X8,X7] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X6,X7),X8)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X6,X7),X8))) )),
% 2.16/0.69    inference(forward_demodulation,[],[f349,f54])).
% 2.16/0.69  fof(f349,plain,(
% 2.16/0.69    ( ! [X6,X8,X7] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X6,X7),X8)) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X6,X7)),X8)) )),
% 2.16/0.69    inference(superposition,[],[f54,f324])).
% 2.16/0.69  fof(f338,plain,(
% 2.16/0.69    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))))),
% 2.16/0.69    inference(backward_demodulation,[],[f181,f324])).
% 2.16/0.69  fof(f181,plain,(
% 2.16/0.69    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))))),
% 2.16/0.69    inference(forward_demodulation,[],[f180,f40])).
% 2.16/0.69  fof(f180,plain,(
% 2.16/0.69    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k1_xboole_0))))),
% 2.16/0.69    inference(forward_demodulation,[],[f178,f54])).
% 2.16/0.69  fof(f178,plain,(
% 2.16/0.69    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = k3_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k1_xboole_0)))),
% 2.16/0.69    inference(superposition,[],[f78,f130])).
% 2.16/0.69  fof(f130,plain,(
% 2.16/0.69    k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 2.16/0.69    inference(superposition,[],[f114,f45])).
% 2.16/0.69  fof(f808,plain,(
% 2.16/0.69    ( ! [X8] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X8) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,X8))) )),
% 2.16/0.69    inference(backward_demodulation,[],[f752,f807])).
% 2.16/0.69  fof(f807,plain,(
% 2.16/0.69    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0))) )),
% 2.16/0.69    inference(superposition,[],[f54,f776])).
% 2.16/0.69  fof(f776,plain,(
% 2.16/0.69    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.16/0.69    inference(forward_demodulation,[],[f763,f40])).
% 2.16/0.69  fof(f763,plain,(
% 2.16/0.69    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.16/0.69    inference(superposition,[],[f717,f575])).
% 2.16/0.69  fof(f752,plain,(
% 2.16/0.69    ( ! [X8] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X8)) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k1_xboole_0,X8))) )),
% 2.16/0.69    inference(superposition,[],[f717,f717])).
% 2.16/0.69  fof(f95,plain,(
% 2.16/0.69    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 2.16/0.69    inference(equality_resolution,[],[f88])).
% 2.16/0.69  fof(f88,plain,(
% 2.16/0.69    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.16/0.69    inference(definition_unfolding,[],[f57,f72])).
% 2.16/0.69  fof(f57,plain,(
% 2.16/0.69    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.16/0.69    inference(cnf_transformation,[],[f37])).
% 2.16/0.69  % SZS output end Proof for theBenchmark
% 2.16/0.69  % (30527)------------------------------
% 2.16/0.69  % (30527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.69  % (30527)Termination reason: Refutation
% 2.16/0.69  
% 2.16/0.69  % (30527)Memory used [KB]: 11769
% 2.16/0.69  % (30527)Time elapsed: 0.254 s
% 2.16/0.69  % (30527)------------------------------
% 2.16/0.69  % (30527)------------------------------
% 2.16/0.69  % (30518)Success in time 0.329 s
%------------------------------------------------------------------------------
