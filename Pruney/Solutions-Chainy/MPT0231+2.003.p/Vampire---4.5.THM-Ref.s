%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:54 EST 2020

% Result     : Theorem 4.93s
% Output     : Refutation 4.93s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 365 expanded)
%              Number of leaves         :   19 ( 126 expanded)
%              Depth                    :   19
%              Number of atoms          :  434 ( 991 expanded)
%              Number of equality atoms :  362 ( 869 expanded)
%              Maximal formula depth    :   27 (   9 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2237,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f188,f210,f720,f2235])).

fof(f2235,plain,
    ( spl5_1
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f2234])).

fof(f2234,plain,
    ( $false
    | spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f2217,f1268])).

fof(f1268,plain,
    ( ! [X0] : r2_hidden(sK0,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | ~ spl5_5 ),
    inference(superposition,[],[f354,f719])).

fof(f719,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f717])).

fof(f717,plain,
    ( spl5_5
  <=> k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f354,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : r2_hidden(X8,k2_xboole_0(k5_enumset1(X9,X9,X9,X9,X9,X9,X9),k2_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))) ),
    inference(forward_demodulation,[],[f348,f91])).

fof(f91,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(definition_unfolding,[],[f53,f83,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) ),
    inference(definition_unfolding,[],[f52,f81,f82])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(definition_unfolding,[],[f51,f81])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

fof(f81,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f80])).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_enumset1)).

fof(f348,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : r2_hidden(X8,k2_xboole_0(k5_enumset1(X9,X9,X9,X9,X9,X9,X9),k2_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k2_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))))) ),
    inference(superposition,[],[f179,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f179,plain,(
    ! [X6,X4,X2,X0,X12,X8,X7,X5,X3,X9] : r2_hidden(X12,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X12,X12,X12,X12,X12,X12,X12),k2_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X9,X9,X9,X9,X9,X9,X9))))) ),
    inference(forward_demodulation,[],[f178,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f178,plain,(
    ! [X6,X4,X2,X0,X12,X8,X7,X5,X3,X9] : r2_hidden(X12,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k2_xboole_0(k5_enumset1(X12,X12,X12,X12,X12,X12,X12),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)),k5_enumset1(X9,X9,X9,X9,X9,X9,X9)))) ),
    inference(forward_demodulation,[],[f135,f46])).

fof(f135,plain,(
    ! [X6,X4,X2,X0,X12,X8,X7,X5,X3,X9] : r2_hidden(X12,k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X12,X12,X12,X12,X12,X12,X12),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),k5_enumset1(X9,X9,X9,X9,X9,X9,X9))) ),
    inference(equality_resolution,[],[f134])).

fof(f134,plain,(
    ! [X6,X4,X2,X0,X12,X10,X8,X7,X5,X3,X9] :
      ( r2_hidden(X12,X10)
      | k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X12,X12,X12,X12,X12,X12,X12),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),k5_enumset1(X9,X9,X9,X9,X9,X9,X9)) != X10 ) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X6,X4,X2,X0,X12,X10,X8,X7,X5,X3,X1,X9] :
      ( r2_hidden(X12,X10)
      | X1 != X12
      | k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),k5_enumset1(X9,X9,X9,X9,X9,X9,X9)) != X10 ) ),
    inference(definition_unfolding,[],[f58,f84])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),k5_enumset1(X9,X9,X9,X9,X9,X9,X9)) ),
    inference(definition_unfolding,[],[f55,f83,f81])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_enumset1)).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X12,X10,X8,X7,X5,X3,X1,X9] :
      ( r2_hidden(X12,X10)
      | X1 != X12
      | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( ( k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10
        | ( ( ( sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X9
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X8
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X7
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X6
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X5
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X4
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X3
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X2
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X1
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10) )
          & ( sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X9
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X8
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X7
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X6
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X5
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X4
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X3
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X2
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X1
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X0
            | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10) ) ) )
      & ( ! [X12] :
            ( ( r2_hidden(X12,X10)
              | ( X9 != X12
                & X8 != X12
                & X7 != X12
                & X6 != X12
                & X5 != X12
                & X4 != X12
                & X3 != X12
                & X2 != X12
                & X1 != X12
                & X0 != X12 ) )
            & ( X9 = X12
              | X8 = X12
              | X7 = X12
              | X6 = X12
              | X5 = X12
              | X4 = X12
              | X3 = X12
              | X2 = X12
              | X1 = X12
              | X0 = X12
              | ~ r2_hidden(X12,X10) ) )
        | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X10,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X11] :
          ( ( ( X9 != X11
              & X8 != X11
              & X7 != X11
              & X6 != X11
              & X5 != X11
              & X4 != X11
              & X3 != X11
              & X2 != X11
              & X1 != X11
              & X0 != X11 )
            | ~ r2_hidden(X11,X10) )
          & ( X9 = X11
            | X8 = X11
            | X7 = X11
            | X6 = X11
            | X5 = X11
            | X4 = X11
            | X3 = X11
            | X2 = X11
            | X1 = X11
            | X0 = X11
            | r2_hidden(X11,X10) ) )
     => ( ( ( sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X9
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X8
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X7
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X6
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X5
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X4
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X3
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X2
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X1
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10) )
        & ( sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X9
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X8
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X7
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X6
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X5
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X4
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X3
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X2
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X1
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X0
          | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( ( k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10
        | ? [X11] :
            ( ( ( X9 != X11
                & X8 != X11
                & X7 != X11
                & X6 != X11
                & X5 != X11
                & X4 != X11
                & X3 != X11
                & X2 != X11
                & X1 != X11
                & X0 != X11 )
              | ~ r2_hidden(X11,X10) )
            & ( X9 = X11
              | X8 = X11
              | X7 = X11
              | X6 = X11
              | X5 = X11
              | X4 = X11
              | X3 = X11
              | X2 = X11
              | X1 = X11
              | X0 = X11
              | r2_hidden(X11,X10) ) ) )
      & ( ! [X12] :
            ( ( r2_hidden(X12,X10)
              | ( X9 != X12
                & X8 != X12
                & X7 != X12
                & X6 != X12
                & X5 != X12
                & X4 != X12
                & X3 != X12
                & X2 != X12
                & X1 != X12
                & X0 != X12 ) )
            & ( X9 = X12
              | X8 = X12
              | X7 = X12
              | X6 = X12
              | X5 = X12
              | X4 = X12
              | X3 = X12
              | X2 = X12
              | X1 = X12
              | X0 = X12
              | ~ r2_hidden(X12,X10) ) )
        | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( ( k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10
        | ? [X11] :
            ( ( ( X9 != X11
                & X8 != X11
                & X7 != X11
                & X6 != X11
                & X5 != X11
                & X4 != X11
                & X3 != X11
                & X2 != X11
                & X1 != X11
                & X0 != X11 )
              | ~ r2_hidden(X11,X10) )
            & ( X9 = X11
              | X8 = X11
              | X7 = X11
              | X6 = X11
              | X5 = X11
              | X4 = X11
              | X3 = X11
              | X2 = X11
              | X1 = X11
              | X0 = X11
              | r2_hidden(X11,X10) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X10)
              | ( X9 != X11
                & X8 != X11
                & X7 != X11
                & X6 != X11
                & X5 != X11
                & X4 != X11
                & X3 != X11
                & X2 != X11
                & X1 != X11
                & X0 != X11 ) )
            & ( X9 = X11
              | X8 = X11
              | X7 = X11
              | X6 = X11
              | X5 = X11
              | X4 = X11
              | X3 = X11
              | X2 = X11
              | X1 = X11
              | X0 = X11
              | ~ r2_hidden(X11,X10) ) )
        | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( ( k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10
        | ? [X11] :
            ( ( ( X9 != X11
                & X8 != X11
                & X7 != X11
                & X6 != X11
                & X5 != X11
                & X4 != X11
                & X3 != X11
                & X2 != X11
                & X1 != X11
                & X0 != X11 )
              | ~ r2_hidden(X11,X10) )
            & ( X9 = X11
              | X8 = X11
              | X7 = X11
              | X6 = X11
              | X5 = X11
              | X4 = X11
              | X3 = X11
              | X2 = X11
              | X1 = X11
              | X0 = X11
              | r2_hidden(X11,X10) ) ) )
      & ( ! [X11] :
            ( ( r2_hidden(X11,X10)
              | ( X9 != X11
                & X8 != X11
                & X7 != X11
                & X6 != X11
                & X5 != X11
                & X4 != X11
                & X3 != X11
                & X2 != X11
                & X1 != X11
                & X0 != X11 ) )
            & ( X9 = X11
              | X8 = X11
              | X7 = X11
              | X6 = X11
              | X5 = X11
              | X4 = X11
              | X3 = X11
              | X2 = X11
              | X1 = X11
              | X0 = X11
              | ~ r2_hidden(X11,X10) ) )
        | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10
    <=> ! [X11] :
          ( r2_hidden(X11,X10)
        <=> ( X9 = X11
            | X8 = X11
            | X7 = X11
            | X6 = X11
            | X5 = X11
            | X4 = X11
            | X3 = X11
            | X2 = X11
            | X1 = X11
            | X0 = X11 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] :
      ( k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10
    <=> ! [X11] :
          ( r2_hidden(X11,X10)
        <=> ~ ( X9 != X11
              & X8 != X11
              & X7 != X11
              & X6 != X11
              & X5 != X11
              & X4 != X11
              & X3 != X11
              & X2 != X11
              & X1 != X11
              & X0 != X11 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_enumset1)).

fof(f2217,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f187,f187,f187,f187,f187,f187,f187,f187,f187,f506])).

fof(f506,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( ~ r2_hidden(X9,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)))
      | X1 = X9
      | X8 = X9
      | X7 = X9
      | X6 = X9
      | X5 = X9
      | X4 = X9
      | X3 = X9
      | X2 = X9
      | X0 = X9 ) ),
    inference(duplicate_literal_removal,[],[f503])).

fof(f503,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] :
      ( ~ r2_hidden(X9,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)))
      | X1 = X9
      | X8 = X9
      | X7 = X9
      | X6 = X9
      | X5 = X9
      | X4 = X9
      | X3 = X9
      | X2 = X9
      | X1 = X9
      | X0 = X9 ) ),
    inference(superposition,[],[f416,f91])).

fof(f416,plain,(
    ! [X6,X4,X2,X0,X12,X8,X7,X5,X3,X1,X9] :
      ( ~ r2_hidden(X12,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X9),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))))
      | X9 = X12
      | X8 = X12
      | X7 = X12
      | X6 = X12
      | X5 = X12
      | X4 = X12
      | X3 = X12
      | X2 = X12
      | X1 = X12
      | X0 = X12 ) ),
    inference(backward_demodulation,[],[f183,f376])).

fof(f376,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k2_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) ),
    inference(superposition,[],[f91,f39])).

fof(f183,plain,(
    ! [X6,X4,X2,X0,X12,X8,X7,X5,X3,X1,X9] :
      ( ~ r2_hidden(X12,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k2_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X9,X9,X9,X9,X9,X9,X9)))))
      | X9 = X12
      | X8 = X12
      | X7 = X12
      | X6 = X12
      | X5 = X12
      | X4 = X12
      | X3 = X12
      | X2 = X12
      | X1 = X12
      | X0 = X12 ) ),
    inference(forward_demodulation,[],[f182,f46])).

fof(f182,plain,(
    ! [X6,X4,X2,X0,X12,X8,X7,X5,X3,X1,X9] :
      ( ~ r2_hidden(X12,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)),k5_enumset1(X9,X9,X9,X9,X9,X9,X9))))
      | X9 = X12
      | X8 = X12
      | X7 = X12
      | X6 = X12
      | X5 = X12
      | X4 = X12
      | X3 = X12
      | X2 = X12
      | X1 = X12
      | X0 = X12 ) ),
    inference(forward_demodulation,[],[f138,f46])).

fof(f138,plain,(
    ! [X6,X4,X2,X0,X12,X8,X7,X5,X3,X1,X9] :
      ( X9 = X12
      | X8 = X12
      | X7 = X12
      | X6 = X12
      | X5 = X12
      | X4 = X12
      | X3 = X12
      | X2 = X12
      | X1 = X12
      | X0 = X12
      | ~ r2_hidden(X12,k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),k5_enumset1(X9,X9,X9,X9,X9,X9,X9))) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X6,X4,X2,X0,X12,X10,X8,X7,X5,X3,X1,X9] :
      ( X9 = X12
      | X8 = X12
      | X7 = X12
      | X6 = X12
      | X5 = X12
      | X4 = X12
      | X3 = X12
      | X2 = X12
      | X1 = X12
      | X0 = X12
      | ~ r2_hidden(X12,X10)
      | k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),k5_enumset1(X9,X9,X9,X9,X9,X9,X9)) != X10 ) ),
    inference(definition_unfolding,[],[f56,f84])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X12,X10,X8,X7,X5,X3,X1,X9] :
      ( X9 = X12
      | X8 = X12
      | X7 = X12
      | X6 = X12
      | X5 = X12
      | X4 = X12
      | X3 = X12
      | X2 = X12
      | X1 = X12
      | X0 = X12
      | ~ r2_hidden(X12,X10)
      | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f187,plain,
    ( sK0 != sK2
    | spl5_1 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl5_1
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f720,plain,
    ( spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f213,f207,f717])).

fof(f207,plain,
    ( spl5_2
  <=> r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f213,plain,
    ( k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f209,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f209,plain,
    ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f207])).

fof(f210,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f85,f207])).

fof(f85,plain,(
    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f35,f80,f81])).

fof(f35,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f188,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f36,f185])).

fof(f36,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (19908)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.52  % (19892)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (19890)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (19897)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (19884)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (19906)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (19905)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (19887)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (19885)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (19893)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (19899)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (19886)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (19912)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (19904)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (19902)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (19889)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (19898)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (19901)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (19883)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (19888)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (19896)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (19911)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (19893)Refutation not found, incomplete strategy% (19893)------------------------------
% 0.20/0.55  % (19893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (19909)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (19912)Refutation not found, incomplete strategy% (19912)------------------------------
% 0.20/0.55  % (19912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (19912)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (19912)Memory used [KB]: 1663
% 0.20/0.55  % (19912)Time elapsed: 0.002 s
% 0.20/0.55  % (19912)------------------------------
% 0.20/0.55  % (19912)------------------------------
% 0.20/0.55  % (19891)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (19903)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (19910)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (19900)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.56  % (19899)Refutation not found, incomplete strategy% (19899)------------------------------
% 0.20/0.56  % (19899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (19899)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (19899)Memory used [KB]: 10746
% 0.20/0.56  % (19899)Time elapsed: 0.147 s
% 0.20/0.56  % (19899)------------------------------
% 0.20/0.56  % (19899)------------------------------
% 0.20/0.56  % (19894)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.56  % (19895)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.56  % (19907)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.56  % (19893)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (19893)Memory used [KB]: 10746
% 0.20/0.56  % (19893)Time elapsed: 0.144 s
% 0.20/0.56  % (19893)------------------------------
% 0.20/0.56  % (19893)------------------------------
% 0.20/0.57  % (19911)Refutation not found, incomplete strategy% (19911)------------------------------
% 0.20/0.57  % (19911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (19911)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (19911)Memory used [KB]: 10874
% 0.20/0.58  % (19911)Time elapsed: 0.144 s
% 0.20/0.58  % (19911)------------------------------
% 0.20/0.58  % (19911)------------------------------
% 2.09/0.68  % (19943)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.09/0.69  % (19886)Refutation not found, incomplete strategy% (19886)------------------------------
% 2.09/0.69  % (19886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.69  % (19886)Termination reason: Refutation not found, incomplete strategy
% 2.09/0.69  
% 2.09/0.69  % (19886)Memory used [KB]: 6140
% 2.09/0.69  % (19886)Time elapsed: 0.257 s
% 2.09/0.69  % (19886)------------------------------
% 2.09/0.69  % (19886)------------------------------
% 2.09/0.69  % (19939)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.09/0.70  % (19949)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.75/0.71  % (19955)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.17/0.83  % (19885)Time limit reached!
% 3.17/0.83  % (19885)------------------------------
% 3.17/0.83  % (19885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.17/0.84  % (19885)Termination reason: Time limit
% 3.17/0.84  % (19885)Termination phase: Saturation
% 3.17/0.84  
% 3.17/0.84  % (19885)Memory used [KB]: 7291
% 3.17/0.84  % (19885)Time elapsed: 0.400 s
% 3.17/0.84  % (19885)------------------------------
% 3.17/0.84  % (19885)------------------------------
% 3.17/0.85  % (19907)Time limit reached!
% 3.17/0.85  % (19907)------------------------------
% 3.17/0.85  % (19907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.17/0.85  % (19907)Termination reason: Time limit
% 3.17/0.85  
% 3.17/0.85  % (19907)Memory used [KB]: 13176
% 3.17/0.85  % (19907)Time elapsed: 0.416 s
% 3.17/0.85  % (19907)------------------------------
% 3.17/0.85  % (19907)------------------------------
% 3.17/0.85  % (20015)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.38/0.95  % (19897)Time limit reached!
% 4.38/0.95  % (19897)------------------------------
% 4.38/0.95  % (19897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.38/0.97  % (20074)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.38/0.97  % (19897)Termination reason: Time limit
% 4.38/0.97  
% 4.38/0.97  % (19897)Memory used [KB]: 6652
% 4.38/0.97  % (19897)Time elapsed: 0.517 s
% 4.38/0.97  % (19897)------------------------------
% 4.38/0.97  % (19897)------------------------------
% 4.38/0.98  % (20078)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.38/0.99  % (19889)Time limit reached!
% 4.38/0.99  % (19889)------------------------------
% 4.38/0.99  % (19889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.38/0.99  % (19889)Termination reason: Time limit
% 4.38/0.99  
% 4.38/0.99  % (19889)Memory used [KB]: 14200
% 4.38/0.99  % (19889)Time elapsed: 0.540 s
% 4.38/0.99  % (19889)------------------------------
% 4.38/0.99  % (19889)------------------------------
% 4.93/1.04  % (19903)Refutation found. Thanks to Tanya!
% 4.93/1.04  % SZS status Theorem for theBenchmark
% 4.93/1.04  % SZS output start Proof for theBenchmark
% 4.93/1.04  fof(f2237,plain,(
% 4.93/1.04    $false),
% 4.93/1.04    inference(avatar_sat_refutation,[],[f188,f210,f720,f2235])).
% 4.93/1.04  fof(f2235,plain,(
% 4.93/1.04    spl5_1 | ~spl5_5),
% 4.93/1.04    inference(avatar_contradiction_clause,[],[f2234])).
% 4.93/1.04  fof(f2234,plain,(
% 4.93/1.04    $false | (spl5_1 | ~spl5_5)),
% 4.93/1.04    inference(subsumption_resolution,[],[f2217,f1268])).
% 4.93/1.04  fof(f1268,plain,(
% 4.93/1.04    ( ! [X0] : (r2_hidden(sK0,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ) | ~spl5_5),
% 4.93/1.04    inference(superposition,[],[f354,f719])).
% 4.93/1.04  fof(f719,plain,(
% 4.93/1.04    k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_5),
% 4.93/1.04    inference(avatar_component_clause,[],[f717])).
% 4.93/1.04  fof(f717,plain,(
% 4.93/1.04    spl5_5 <=> k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 4.93/1.04    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 4.93/1.04  fof(f354,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (r2_hidden(X8,k2_xboole_0(k5_enumset1(X9,X9,X9,X9,X9,X9,X9),k2_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))))) )),
% 4.93/1.04    inference(forward_demodulation,[],[f348,f91])).
% 4.93/1.04  fof(f91,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) )),
% 4.93/1.04    inference(definition_unfolding,[],[f53,f83,f80])).
% 4.93/1.04  fof(f80,plain,(
% 4.93/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 4.93/1.04    inference(definition_unfolding,[],[f40,f79])).
% 4.93/1.04  fof(f79,plain,(
% 4.93/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 4.93/1.04    inference(definition_unfolding,[],[f48,f78])).
% 4.93/1.04  fof(f78,plain,(
% 4.93/1.04    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 4.93/1.04    inference(definition_unfolding,[],[f49,f50])).
% 4.93/1.04  fof(f50,plain,(
% 4.93/1.04    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 4.93/1.04    inference(cnf_transformation,[],[f15])).
% 4.93/1.04  fof(f15,axiom,(
% 4.93/1.04    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 4.93/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 4.93/1.04  fof(f49,plain,(
% 4.93/1.04    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 4.93/1.04    inference(cnf_transformation,[],[f14])).
% 4.93/1.04  fof(f14,axiom,(
% 4.93/1.04    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 4.93/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 4.93/1.04  fof(f48,plain,(
% 4.93/1.04    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 4.93/1.04    inference(cnf_transformation,[],[f13])).
% 4.93/1.04  fof(f13,axiom,(
% 4.93/1.04    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 4.93/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 4.93/1.04  fof(f40,plain,(
% 4.93/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 4.93/1.04    inference(cnf_transformation,[],[f16])).
% 4.93/1.04  fof(f16,axiom,(
% 4.93/1.04    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 4.93/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 4.93/1.04  fof(f83,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)))) )),
% 4.93/1.04    inference(definition_unfolding,[],[f52,f81,f82])).
% 4.93/1.04  fof(f82,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) )),
% 4.93/1.04    inference(definition_unfolding,[],[f51,f81])).
% 4.93/1.04  fof(f51,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) )),
% 4.93/1.04    inference(cnf_transformation,[],[f11])).
% 4.93/1.04  fof(f11,axiom,(
% 4.93/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 4.93/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).
% 4.93/1.04  fof(f81,plain,(
% 4.93/1.04    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 4.93/1.04    inference(definition_unfolding,[],[f37,f80])).
% 4.93/1.04  fof(f37,plain,(
% 4.93/1.04    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 4.93/1.04    inference(cnf_transformation,[],[f12])).
% 4.93/1.04  fof(f12,axiom,(
% 4.93/1.04    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 4.93/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 4.93/1.04  fof(f52,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))) )),
% 4.93/1.04    inference(cnf_transformation,[],[f7])).
% 4.93/1.04  fof(f7,axiom,(
% 4.93/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))),
% 4.93/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).
% 4.93/1.04  fof(f53,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) )),
% 4.93/1.04    inference(cnf_transformation,[],[f8])).
% 4.93/1.04  fof(f8,axiom,(
% 4.93/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),
% 4.93/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_enumset1)).
% 4.93/1.04  fof(f348,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (r2_hidden(X8,k2_xboole_0(k5_enumset1(X9,X9,X9,X9,X9,X9,X9),k2_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k2_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))))) )),
% 4.93/1.04    inference(superposition,[],[f179,f39])).
% 4.93/1.04  fof(f39,plain,(
% 4.93/1.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.93/1.04    inference(cnf_transformation,[],[f1])).
% 4.93/1.04  fof(f1,axiom,(
% 4.93/1.04    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.93/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.93/1.04  fof(f179,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X12,X8,X7,X5,X3,X9] : (r2_hidden(X12,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X12,X12,X12,X12,X12,X12,X12),k2_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X9,X9,X9,X9,X9,X9,X9)))))) )),
% 4.93/1.04    inference(forward_demodulation,[],[f178,f46])).
% 4.93/1.04  fof(f46,plain,(
% 4.93/1.04    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.93/1.04    inference(cnf_transformation,[],[f4])).
% 4.93/1.04  fof(f4,axiom,(
% 4.93/1.04    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.93/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 4.93/1.04  fof(f178,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X12,X8,X7,X5,X3,X9] : (r2_hidden(X12,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k2_xboole_0(k5_enumset1(X12,X12,X12,X12,X12,X12,X12),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)),k5_enumset1(X9,X9,X9,X9,X9,X9,X9))))) )),
% 4.93/1.04    inference(forward_demodulation,[],[f135,f46])).
% 4.93/1.04  fof(f135,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X12,X8,X7,X5,X3,X9] : (r2_hidden(X12,k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X12,X12,X12,X12,X12,X12,X12),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),k5_enumset1(X9,X9,X9,X9,X9,X9,X9)))) )),
% 4.93/1.04    inference(equality_resolution,[],[f134])).
% 4.93/1.04  fof(f134,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X12,X10,X8,X7,X5,X3,X9] : (r2_hidden(X12,X10) | k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X12,X12,X12,X12,X12,X12,X12),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),k5_enumset1(X9,X9,X9,X9,X9,X9,X9)) != X10) )),
% 4.93/1.04    inference(equality_resolution,[],[f112])).
% 4.93/1.04  fof(f112,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X12,X10,X8,X7,X5,X3,X1,X9] : (r2_hidden(X12,X10) | X1 != X12 | k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),k5_enumset1(X9,X9,X9,X9,X9,X9,X9)) != X10) )),
% 4.93/1.04    inference(definition_unfolding,[],[f58,f84])).
% 4.93/1.04  fof(f84,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),k5_enumset1(X9,X9,X9,X9,X9,X9,X9))) )),
% 4.93/1.04    inference(definition_unfolding,[],[f55,f83,f81])).
% 4.93/1.04  fof(f55,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9))) )),
% 4.93/1.04    inference(cnf_transformation,[],[f10])).
% 4.93/1.04  fof(f10,axiom,(
% 4.93/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9] : k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = k2_xboole_0(k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8),k1_tarski(X9))),
% 4.93/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_enumset1)).
% 4.93/1.04  fof(f58,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X12,X10,X8,X7,X5,X3,X1,X9] : (r2_hidden(X12,X10) | X1 != X12 | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10) )),
% 4.93/1.04    inference(cnf_transformation,[],[f34])).
% 4.93/1.04  fof(f34,plain,(
% 4.93/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : ((k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10 | (((sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X9 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X8 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X7 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X6 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X5 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X4 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X3 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X2 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X1 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10)) & (sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X9 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X8 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X7 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X6 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X5 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X4 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X3 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X2 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X1 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X0 | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10)))) & (! [X12] : ((r2_hidden(X12,X10) | (X9 != X12 & X8 != X12 & X7 != X12 & X6 != X12 & X5 != X12 & X4 != X12 & X3 != X12 & X2 != X12 & X1 != X12 & X0 != X12)) & (X9 = X12 | X8 = X12 | X7 = X12 | X6 = X12 | X5 = X12 | X4 = X12 | X3 = X12 | X2 = X12 | X1 = X12 | X0 = X12 | ~r2_hidden(X12,X10))) | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10))),
% 4.93/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 4.93/1.04  fof(f33,plain,(
% 4.93/1.04    ! [X10,X9,X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X11] : (((X9 != X11 & X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11) | ~r2_hidden(X11,X10)) & (X9 = X11 | X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | r2_hidden(X11,X10))) => (((sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X9 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X8 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X7 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X6 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X5 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X4 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X3 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X2 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X1 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10)) & (sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X9 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X8 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X7 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X6 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X5 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X4 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X3 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X2 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X1 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10) = X0 | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10),X10))))),
% 4.93/1.04    introduced(choice_axiom,[])).
% 4.93/1.04  fof(f32,plain,(
% 4.93/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : ((k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10 | ? [X11] : (((X9 != X11 & X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11) | ~r2_hidden(X11,X10)) & (X9 = X11 | X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | r2_hidden(X11,X10)))) & (! [X12] : ((r2_hidden(X12,X10) | (X9 != X12 & X8 != X12 & X7 != X12 & X6 != X12 & X5 != X12 & X4 != X12 & X3 != X12 & X2 != X12 & X1 != X12 & X0 != X12)) & (X9 = X12 | X8 = X12 | X7 = X12 | X6 = X12 | X5 = X12 | X4 = X12 | X3 = X12 | X2 = X12 | X1 = X12 | X0 = X12 | ~r2_hidden(X12,X10))) | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10))),
% 4.93/1.04    inference(rectify,[],[f31])).
% 4.93/1.04  fof(f31,plain,(
% 4.93/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : ((k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10 | ? [X11] : (((X9 != X11 & X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11) | ~r2_hidden(X11,X10)) & (X9 = X11 | X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | r2_hidden(X11,X10)))) & (! [X11] : ((r2_hidden(X11,X10) | (X9 != X11 & X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11)) & (X9 = X11 | X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11 | ~r2_hidden(X11,X10))) | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10))),
% 4.93/1.04    inference(flattening,[],[f30])).
% 4.93/1.04  fof(f30,plain,(
% 4.93/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : ((k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10 | ? [X11] : (((X9 != X11 & X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11) | ~r2_hidden(X11,X10)) & ((X9 = X11 | X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11) | r2_hidden(X11,X10)))) & (! [X11] : ((r2_hidden(X11,X10) | (X9 != X11 & X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11)) & ((X9 = X11 | X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11) | ~r2_hidden(X11,X10))) | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10))),
% 4.93/1.04    inference(nnf_transformation,[],[f23])).
% 4.93/1.04  fof(f23,plain,(
% 4.93/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : (k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10 <=> ! [X11] : (r2_hidden(X11,X10) <=> (X9 = X11 | X8 = X11 | X7 = X11 | X6 = X11 | X5 = X11 | X4 = X11 | X3 = X11 | X2 = X11 | X1 = X11 | X0 = X11)))),
% 4.93/1.04    inference(ennf_transformation,[],[f6])).
% 4.93/1.04  fof(f6,axiom,(
% 4.93/1.04    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8,X9,X10] : (k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) = X10 <=> ! [X11] : (r2_hidden(X11,X10) <=> ~(X9 != X11 & X8 != X11 & X7 != X11 & X6 != X11 & X5 != X11 & X4 != X11 & X3 != X11 & X2 != X11 & X1 != X11 & X0 != X11)))),
% 4.93/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_enumset1)).
% 4.93/1.04  fof(f2217,plain,(
% 4.93/1.04    ~r2_hidden(sK0,k2_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | spl5_1),
% 4.93/1.04    inference(unit_resulting_resolution,[],[f187,f187,f187,f187,f187,f187,f187,f187,f187,f506])).
% 4.93/1.04  fof(f506,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (~r2_hidden(X9,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) | X1 = X9 | X8 = X9 | X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X0 = X9) )),
% 4.93/1.04    inference(duplicate_literal_removal,[],[f503])).
% 4.93/1.04  fof(f503,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1,X9] : (~r2_hidden(X9,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) | X1 = X9 | X8 = X9 | X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) )),
% 4.93/1.04    inference(superposition,[],[f416,f91])).
% 4.93/1.04  fof(f416,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X12,X8,X7,X5,X3,X1,X9] : (~r2_hidden(X12,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X9),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)))) | X9 = X12 | X8 = X12 | X7 = X12 | X6 = X12 | X5 = X12 | X4 = X12 | X3 = X12 | X2 = X12 | X1 = X12 | X0 = X12) )),
% 4.93/1.04    inference(backward_demodulation,[],[f183,f376])).
% 4.93/1.04  fof(f376,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k2_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k2_xboole_0(k5_enumset1(X1,X2,X3,X4,X5,X6,X7),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) )),
% 4.93/1.04    inference(superposition,[],[f91,f39])).
% 4.93/1.04  fof(f183,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X12,X8,X7,X5,X3,X1,X9] : (~r2_hidden(X12,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k2_xboole_0(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k5_enumset1(X9,X9,X9,X9,X9,X9,X9))))) | X9 = X12 | X8 = X12 | X7 = X12 | X6 = X12 | X5 = X12 | X4 = X12 | X3 = X12 | X2 = X12 | X1 = X12 | X0 = X12) )),
% 4.93/1.04    inference(forward_demodulation,[],[f182,f46])).
% 4.93/1.04  fof(f182,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X12,X8,X7,X5,X3,X1,X9] : (~r2_hidden(X12,k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)),k5_enumset1(X9,X9,X9,X9,X9,X9,X9)))) | X9 = X12 | X8 = X12 | X7 = X12 | X6 = X12 | X5 = X12 | X4 = X12 | X3 = X12 | X2 = X12 | X1 = X12 | X0 = X12) )),
% 4.93/1.04    inference(forward_demodulation,[],[f138,f46])).
% 4.93/1.04  fof(f138,plain,(
% 4.93/1.04    ( ! [X6,X4,X2,X0,X12,X8,X7,X5,X3,X1,X9] : (X9 = X12 | X8 = X12 | X7 = X12 | X6 = X12 | X5 = X12 | X4 = X12 | X3 = X12 | X2 = X12 | X1 = X12 | X0 = X12 | ~r2_hidden(X12,k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),k5_enumset1(X9,X9,X9,X9,X9,X9,X9)))) )),
% 4.93/1.04    inference(equality_resolution,[],[f114])).
% 4.93/1.05  fof(f114,plain,(
% 4.93/1.05    ( ! [X6,X4,X2,X0,X12,X10,X8,X7,X5,X3,X1,X9] : (X9 = X12 | X8 = X12 | X7 = X12 | X6 = X12 | X5 = X12 | X4 = X12 | X3 = X12 | X2 = X12 | X1 = X12 | X0 = X12 | ~r2_hidden(X12,X10) | k2_xboole_0(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),k5_enumset1(X9,X9,X9,X9,X9,X9,X9)) != X10) )),
% 4.93/1.05    inference(definition_unfolding,[],[f56,f84])).
% 4.93/1.05  fof(f56,plain,(
% 4.93/1.05    ( ! [X6,X4,X2,X0,X12,X10,X8,X7,X5,X3,X1,X9] : (X9 = X12 | X8 = X12 | X7 = X12 | X6 = X12 | X5 = X12 | X4 = X12 | X3 = X12 | X2 = X12 | X1 = X12 | X0 = X12 | ~r2_hidden(X12,X10) | k8_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8,X9) != X10) )),
% 4.93/1.05    inference(cnf_transformation,[],[f34])).
% 4.93/1.05  fof(f187,plain,(
% 4.93/1.05    sK0 != sK2 | spl5_1),
% 4.93/1.05    inference(avatar_component_clause,[],[f185])).
% 4.93/1.05  fof(f185,plain,(
% 4.93/1.05    spl5_1 <=> sK0 = sK2),
% 4.93/1.05    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 4.93/1.05  fof(f720,plain,(
% 4.93/1.05    spl5_5 | ~spl5_2),
% 4.93/1.05    inference(avatar_split_clause,[],[f213,f207,f717])).
% 4.93/1.05  fof(f207,plain,(
% 4.93/1.05    spl5_2 <=> r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 4.93/1.05    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 4.93/1.05  fof(f213,plain,(
% 4.93/1.05    k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_2),
% 4.93/1.05    inference(unit_resulting_resolution,[],[f209,f41])).
% 4.93/1.05  fof(f41,plain,(
% 4.93/1.05    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 4.93/1.05    inference(cnf_transformation,[],[f21])).
% 4.93/1.05  fof(f21,plain,(
% 4.93/1.05    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.93/1.05    inference(ennf_transformation,[],[f3])).
% 4.93/1.05  fof(f3,axiom,(
% 4.93/1.05    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.93/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 4.93/1.05  fof(f209,plain,(
% 4.93/1.05    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl5_2),
% 4.93/1.05    inference(avatar_component_clause,[],[f207])).
% 4.93/1.05  fof(f210,plain,(
% 4.93/1.05    spl5_2),
% 4.93/1.05    inference(avatar_split_clause,[],[f85,f207])).
% 4.93/1.05  fof(f85,plain,(
% 4.93/1.05    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 4.93/1.05    inference(definition_unfolding,[],[f35,f80,f81])).
% 4.93/1.05  fof(f35,plain,(
% 4.93/1.05    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 4.93/1.05    inference(cnf_transformation,[],[f25])).
% 4.93/1.05  fof(f25,plain,(
% 4.93/1.05    sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 4.93/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24])).
% 4.93/1.05  fof(f24,plain,(
% 4.93/1.05    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)))),
% 4.93/1.05    introduced(choice_axiom,[])).
% 4.93/1.05  fof(f20,plain,(
% 4.93/1.05    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 4.93/1.05    inference(ennf_transformation,[],[f19])).
% 4.93/1.05  fof(f19,negated_conjecture,(
% 4.93/1.05    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 4.93/1.05    inference(negated_conjecture,[],[f18])).
% 4.93/1.05  fof(f18,conjecture,(
% 4.93/1.05    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 4.93/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 4.93/1.05  fof(f188,plain,(
% 4.93/1.05    ~spl5_1),
% 4.93/1.05    inference(avatar_split_clause,[],[f36,f185])).
% 4.93/1.05  fof(f36,plain,(
% 4.93/1.05    sK0 != sK2),
% 4.93/1.05    inference(cnf_transformation,[],[f25])).
% 4.93/1.05  % SZS output end Proof for theBenchmark
% 4.93/1.05  % (19903)------------------------------
% 4.93/1.05  % (19903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.93/1.05  % (19903)Termination reason: Refutation
% 4.93/1.05  
% 4.93/1.05  % (19903)Memory used [KB]: 14583
% 4.93/1.05  % (19903)Time elapsed: 0.597 s
% 4.93/1.05  % (19903)------------------------------
% 4.93/1.05  % (19903)------------------------------
% 4.93/1.05  % (19882)Success in time 0.686 s
%------------------------------------------------------------------------------
