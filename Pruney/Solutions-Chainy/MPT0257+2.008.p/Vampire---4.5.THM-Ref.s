%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:03 EST 2020

% Result     : Theorem 11.56s
% Output     : Refutation 11.56s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 695 expanded)
%              Number of leaves         :   16 ( 218 expanded)
%              Depth                    :   20
%              Number of atoms          :  246 (1202 expanded)
%              Number of equality atoms :  148 ( 738 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15689,plain,(
    $false ),
    inference(subsumption_resolution,[],[f15630,f35])).

fof(f35,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0))
        & r2_hidden(X0,X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_zfmisc_1)).

fof(f15630,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f3410,f15629])).

fof(f15629,plain,(
    sK0 = sK2(k1_tarski(sK0),sK1) ),
    inference(condensation,[],[f15623])).

fof(f15623,plain,(
    ! [X0] :
      ( sK2(k1_tarski(sK0),sK1) = X0
      | sK0 = sK2(k1_tarski(sK0),sK1) ) ),
    inference(resolution,[],[f3423,f84])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f50,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f3423,plain,(
    ! [X0] : r2_hidden(sK2(k1_tarski(sK0),sK1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK0)) ),
    inference(unit_resulting_resolution,[],[f85,f86,f3400,f179])).

fof(f179,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X3,X5)
      | r1_tarski(X2,X4)
      | r2_hidden(sK2(X2,X4),X5)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f127,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f127,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(sK2(X1,X2),X3)
      | ~ r1_tarski(X1,X3)
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f43,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3400,plain,(
    ~ r1_tarski(k1_tarski(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f3200,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f3200,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(backward_demodulation,[],[f3123,f3198])).

fof(f3198,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) ),
    inference(forward_demodulation,[],[f3197,f97])).

fof(f97,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f89,f47])).

fof(f89,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f38,f37])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f3197,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) = k4_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f3196,f487])).

fof(f487,plain,(
    ! [X4,X5] : k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4) ),
    inference(superposition,[],[f406,f406])).

fof(f406,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(unit_resulting_resolution,[],[f386,f135])).

fof(f135,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 != k4_xboole_0(X3,k4_xboole_0(X3,X4))
      | k4_xboole_0(X3,X4) = X3 ) ),
    inference(superposition,[],[f42,f96])).

fof(f96,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f38,f47])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f386,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(forward_demodulation,[],[f385,f96])).

fof(f385,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(forward_demodulation,[],[f345,f37])).

fof(f345,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f66,f97])).

fof(f66,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f48,f40,f40,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f3196,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(k4_xboole_0(X3,X2),X2)) = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) ),
    inference(forward_demodulation,[],[f2985,f37])).

fof(f2985,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(k4_xboole_0(X3,X2),X2)) = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f67,f97])).

fof(f67,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1)) ),
    inference(definition_unfolding,[],[f49,f40,f40,f40])).

fof(f49,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).

fof(f3123,plain,(
    k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(sK0))),k1_tarski(sK0)) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(backward_demodulation,[],[f131,f3122])).

fof(f3122,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(forward_demodulation,[],[f3121,f809])).

fof(f809,plain,(
    ! [X54,X52,X53] : k4_xboole_0(X53,X54) = k4_xboole_0(k4_xboole_0(X53,X54),k4_xboole_0(X52,X53)) ),
    inference(superposition,[],[f406,f702])).

fof(f702,plain,(
    ! [X8,X7,X9] : k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X7,X9)) ),
    inference(superposition,[],[f594,f406])).

fof(f594,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0 ),
    inference(unit_resulting_resolution,[],[f463,f135])).

fof(f463,plain,(
    ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X5,X4),X6))) ),
    inference(forward_demodulation,[],[f426,f106])).

fof(f106,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f103,f47])).

fof(f103,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(superposition,[],[f38,f97])).

fof(f426,plain,(
    ! [X6,X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X5,X4),X6))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X4,k4_xboole_0(X4,X6))) ),
    inference(superposition,[],[f66,f386])).

fof(f3121,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),X2)) = k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(forward_demodulation,[],[f2954,f37])).

fof(f2954,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),X2)) = k4_xboole_0(k4_xboole_0(X2,k1_xboole_0),k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(superposition,[],[f67,f97])).

fof(f131,plain,(
    k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(sK0)))) != k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(sK0))),k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f64,f42])).

fof(f64,plain,(
    k1_tarski(sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(sK0))) ),
    inference(definition_unfolding,[],[f36,f40])).

fof(f36,plain,(
    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f86,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(definition_unfolding,[],[f59,f63])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_zfmisc_1)).

fof(f85,plain,(
    ! [X2,X1] : r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) != X0 ) ),
    inference(definition_unfolding,[],[f60,f63,f63])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3410,plain,(
    ~ r2_hidden(sK2(k1_tarski(sK0),sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f3400,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:19:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.46  % (18186)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.49  % (18215)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.49  % (18207)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.50  % (18199)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.50  % (18208)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (18191)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (18188)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (18185)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (18190)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (18198)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (18208)Refutation not found, incomplete strategy% (18208)------------------------------
% 0.22/0.53  % (18208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18208)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (18208)Memory used [KB]: 10746
% 0.22/0.53  % (18208)Time elapsed: 0.085 s
% 0.22/0.53  % (18208)------------------------------
% 0.22/0.53  % (18208)------------------------------
% 0.22/0.53  % (18214)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (18189)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (18197)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.54  % (18209)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.40/0.54  % (18212)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.54  % (18213)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.54  % (18200)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.40/0.55  % (18192)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.40/0.55  % (18204)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.55  % (18205)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.55  % (18206)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.55  % (18193)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.40/0.55  % (18196)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.40/0.55  % (18195)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.53/0.56  % (18201)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.53/0.56  % (18203)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.53/0.57  % (18210)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.53/0.58  % (18187)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.53/0.58  % (18187)Refutation not found, incomplete strategy% (18187)------------------------------
% 1.53/0.58  % (18187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (18187)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (18187)Memory used [KB]: 10746
% 1.53/0.58  % (18187)Time elapsed: 0.145 s
% 1.53/0.58  % (18187)------------------------------
% 1.53/0.58  % (18187)------------------------------
% 1.53/0.58  % (18194)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.53/0.59  % (18211)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.39/0.70  % (18234)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.04/0.78  % (18235)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.04/0.81  % (18190)Time limit reached!
% 3.04/0.81  % (18190)------------------------------
% 3.04/0.81  % (18190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.04/0.81  % (18190)Termination reason: Time limit
% 3.04/0.81  % (18190)Termination phase: Saturation
% 3.04/0.81  
% 3.04/0.81  % (18190)Memory used [KB]: 7547
% 3.04/0.81  % (18190)Time elapsed: 0.408 s
% 3.04/0.81  % (18190)------------------------------
% 3.04/0.81  % (18190)------------------------------
% 3.73/0.90  % (18186)Time limit reached!
% 3.73/0.90  % (18186)------------------------------
% 3.73/0.90  % (18186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.73/0.90  % (18186)Termination reason: Time limit
% 3.73/0.90  
% 3.73/0.90  % (18186)Memory used [KB]: 8315
% 3.73/0.90  % (18186)Time elapsed: 0.513 s
% 3.73/0.90  % (18186)------------------------------
% 3.73/0.90  % (18186)------------------------------
% 3.73/0.90  % (18197)Time limit reached!
% 3.73/0.90  % (18197)------------------------------
% 3.73/0.90  % (18197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.73/0.90  % (18197)Termination reason: Time limit
% 3.73/0.90  % (18197)Termination phase: Saturation
% 3.73/0.90  
% 3.73/0.90  % (18197)Memory used [KB]: 9338
% 3.73/0.90  % (18197)Time elapsed: 0.501 s
% 3.73/0.90  % (18197)------------------------------
% 3.73/0.90  % (18197)------------------------------
% 3.73/0.92  % (18203)Time limit reached!
% 3.73/0.92  % (18203)------------------------------
% 3.73/0.92  % (18203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.73/0.92  % (18203)Termination reason: Time limit
% 3.73/0.92  
% 3.73/0.92  % (18203)Memory used [KB]: 12665
% 3.73/0.92  % (18203)Time elapsed: 0.517 s
% 3.73/0.92  % (18203)------------------------------
% 3.73/0.92  % (18203)------------------------------
% 3.73/0.92  % (18195)Time limit reached!
% 3.73/0.92  % (18195)------------------------------
% 3.73/0.92  % (18195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.73/0.92  % (18195)Termination reason: Time limit
% 3.73/0.92  
% 3.73/0.92  % (18195)Memory used [KB]: 13560
% 3.73/0.92  % (18195)Time elapsed: 0.520 s
% 3.73/0.92  % (18195)------------------------------
% 3.73/0.92  % (18195)------------------------------
% 3.73/0.92  % (18185)Time limit reached!
% 3.73/0.92  % (18185)------------------------------
% 3.73/0.92  % (18185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.73/0.92  % (18185)Termination reason: Time limit
% 3.73/0.92  
% 3.73/0.92  % (18185)Memory used [KB]: 3198
% 3.73/0.92  % (18185)Time elapsed: 0.517 s
% 3.73/0.92  % (18185)------------------------------
% 3.73/0.92  % (18185)------------------------------
% 4.29/0.96  % (18236)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.54/1.00  % (18192)Time limit reached!
% 4.54/1.00  % (18192)------------------------------
% 4.54/1.00  % (18192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/1.00  % (18192)Termination reason: Time limit
% 4.54/1.00  % (18192)Termination phase: Saturation
% 4.54/1.00  
% 4.54/1.00  % (18192)Memory used [KB]: 10874
% 4.54/1.00  % (18192)Time elapsed: 0.600 s
% 4.54/1.00  % (18192)------------------------------
% 4.54/1.00  % (18192)------------------------------
% 4.54/1.00  % (18201)Time limit reached!
% 4.54/1.00  % (18201)------------------------------
% 4.54/1.00  % (18201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/1.00  % (18201)Termination reason: Time limit
% 4.54/1.00  % (18201)Termination phase: Saturation
% 4.54/1.00  
% 4.54/1.00  % (18201)Memory used [KB]: 16886
% 4.54/1.00  % (18201)Time elapsed: 0.600 s
% 4.54/1.00  % (18201)------------------------------
% 4.54/1.00  % (18201)------------------------------
% 4.54/1.01  % (18214)Time limit reached!
% 4.54/1.01  % (18214)------------------------------
% 4.54/1.01  % (18214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/1.01  % (18214)Termination reason: Time limit
% 4.54/1.01  
% 4.54/1.01  % (18214)Memory used [KB]: 9083
% 4.54/1.01  % (18214)Time elapsed: 0.609 s
% 4.54/1.01  % (18214)------------------------------
% 4.54/1.01  % (18214)------------------------------
% 4.54/1.02  % (18238)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.93/1.04  % (18237)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.93/1.05  % (18239)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.93/1.06  % (18241)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.93/1.07  % (18240)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 6.08/1.14  % (18242)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.36/1.17  % (18243)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.36/1.17  % (18244)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.36/1.21  % (18207)Time limit reached!
% 6.36/1.21  % (18207)------------------------------
% 6.36/1.21  % (18207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.36/1.21  % (18207)Termination reason: Time limit
% 6.36/1.21  % (18207)Termination phase: Saturation
% 6.36/1.21  
% 6.36/1.21  % (18207)Memory used [KB]: 2302
% 6.36/1.21  % (18207)Time elapsed: 0.800 s
% 6.36/1.21  % (18207)------------------------------
% 6.36/1.21  % (18207)------------------------------
% 7.63/1.34  % (18237)Time limit reached!
% 7.63/1.34  % (18237)------------------------------
% 7.63/1.34  % (18237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.63/1.34  % (18237)Termination reason: Time limit
% 7.63/1.34  
% 7.63/1.34  % (18237)Memory used [KB]: 7291
% 7.63/1.34  % (18237)Time elapsed: 0.411 s
% 7.63/1.34  % (18237)------------------------------
% 7.63/1.34  % (18237)------------------------------
% 7.91/1.37  % (18245)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 7.91/1.37  % (18238)Time limit reached!
% 7.91/1.37  % (18238)------------------------------
% 7.91/1.37  % (18238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.91/1.39  % (18238)Termination reason: Time limit
% 7.91/1.39  
% 7.91/1.39  % (18238)Memory used [KB]: 13560
% 7.91/1.39  % (18238)Time elapsed: 0.423 s
% 7.91/1.39  % (18238)------------------------------
% 7.91/1.39  % (18238)------------------------------
% 8.63/1.48  % (18246)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.13/1.55  % (18247)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 9.13/1.55  % (18247)Refutation not found, incomplete strategy% (18247)------------------------------
% 9.13/1.55  % (18247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.13/1.55  % (18247)Termination reason: Refutation not found, incomplete strategy
% 9.13/1.55  
% 9.13/1.55  % (18247)Memory used [KB]: 1663
% 9.13/1.55  % (18247)Time elapsed: 0.138 s
% 9.13/1.55  % (18247)------------------------------
% 9.13/1.55  % (18247)------------------------------
% 9.37/1.62  % (18212)Time limit reached!
% 9.37/1.62  % (18212)------------------------------
% 9.37/1.62  % (18212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.37/1.62  % (18212)Termination reason: Time limit
% 9.37/1.62  
% 9.37/1.62  % (18212)Memory used [KB]: 15095
% 9.37/1.62  % (18212)Time elapsed: 1.221 s
% 9.37/1.62  % (18212)------------------------------
% 9.37/1.62  % (18212)------------------------------
% 10.35/1.72  % (18248)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 10.35/1.74  % (18200)Time limit reached!
% 10.35/1.74  % (18200)------------------------------
% 10.35/1.74  % (18200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.35/1.74  % (18200)Termination reason: Time limit
% 10.35/1.74  
% 10.35/1.74  % (18200)Memory used [KB]: 13048
% 10.35/1.74  % (18200)Time elapsed: 1.323 s
% 10.35/1.74  % (18200)------------------------------
% 10.35/1.74  % (18200)------------------------------
% 10.93/1.76  % (18210)Time limit reached!
% 10.93/1.76  % (18210)------------------------------
% 10.93/1.76  % (18210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.93/1.76  % (18210)Termination reason: Time limit
% 10.93/1.76  % (18210)Termination phase: Saturation
% 10.93/1.76  
% 10.93/1.76  % (18210)Memory used [KB]: 19701
% 10.93/1.76  % (18210)Time elapsed: 1.300 s
% 10.93/1.76  % (18210)------------------------------
% 10.93/1.76  % (18210)------------------------------
% 11.14/1.77  % (18249)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.56/1.83  % (18241)Refutation found. Thanks to Tanya!
% 11.56/1.83  % SZS status Theorem for theBenchmark
% 11.56/1.84  % SZS output start Proof for theBenchmark
% 11.56/1.84  fof(f15689,plain,(
% 11.56/1.84    $false),
% 11.56/1.84    inference(subsumption_resolution,[],[f15630,f35])).
% 11.56/1.84  fof(f35,plain,(
% 11.56/1.84    r2_hidden(sK0,sK1)),
% 11.56/1.84    inference(cnf_transformation,[],[f22])).
% 11.56/1.84  fof(f22,plain,(
% 11.56/1.84    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 11.56/1.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f21])).
% 11.56/1.84  fof(f21,plain,(
% 11.56/1.84    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0)) & r2_hidden(X0,X1)) => (k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 11.56/1.84    introduced(choice_axiom,[])).
% 11.56/1.84  fof(f17,plain,(
% 11.56/1.84    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0)) & r2_hidden(X0,X1))),
% 11.56/1.84    inference(ennf_transformation,[],[f16])).
% 11.56/1.84  fof(f16,negated_conjecture,(
% 11.56/1.84    ~! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 11.56/1.84    inference(negated_conjecture,[],[f15])).
% 11.56/1.84  fof(f15,conjecture,(
% 11.56/1.84    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 11.56/1.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_zfmisc_1)).
% 11.56/1.84  fof(f15630,plain,(
% 11.56/1.84    ~r2_hidden(sK0,sK1)),
% 11.56/1.84    inference(backward_demodulation,[],[f3410,f15629])).
% 11.56/1.84  fof(f15629,plain,(
% 11.56/1.84    sK0 = sK2(k1_tarski(sK0),sK1)),
% 11.56/1.84    inference(condensation,[],[f15623])).
% 11.56/1.84  fof(f15623,plain,(
% 11.56/1.84    ( ! [X0] : (sK2(k1_tarski(sK0),sK1) = X0 | sK0 = sK2(k1_tarski(sK0),sK1)) )),
% 11.56/1.84    inference(resolution,[],[f3423,f84])).
% 11.56/1.84  fof(f84,plain,(
% 11.56/1.84    ( ! [X4,X0,X1] : (~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 11.56/1.84    inference(equality_resolution,[],[f73])).
% 11.56/1.84  fof(f73,plain,(
% 11.56/1.84    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 11.56/1.84    inference(definition_unfolding,[],[f50,f63])).
% 11.56/1.84  fof(f63,plain,(
% 11.56/1.84    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.56/1.84    inference(definition_unfolding,[],[f39,f62])).
% 11.56/1.84  fof(f62,plain,(
% 11.56/1.84    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.56/1.84    inference(cnf_transformation,[],[f13])).
% 11.56/1.84  fof(f13,axiom,(
% 11.56/1.84    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)),
% 11.56/1.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_enumset1)).
% 11.56/1.84  fof(f39,plain,(
% 11.56/1.84    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 11.56/1.84    inference(cnf_transformation,[],[f12])).
% 11.56/1.84  fof(f12,axiom,(
% 11.56/1.84    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 11.56/1.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 11.56/1.84  fof(f50,plain,(
% 11.56/1.84    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 11.56/1.84    inference(cnf_transformation,[],[f32])).
% 11.56/1.84  fof(f32,plain,(
% 11.56/1.84    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 11.56/1.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 11.56/1.84  fof(f31,plain,(
% 11.56/1.84    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 11.56/1.84    introduced(choice_axiom,[])).
% 11.56/1.84  fof(f30,plain,(
% 11.56/1.84    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 11.56/1.84    inference(rectify,[],[f29])).
% 11.56/1.84  fof(f29,plain,(
% 11.56/1.84    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 11.56/1.84    inference(flattening,[],[f28])).
% 11.56/1.84  fof(f28,plain,(
% 11.56/1.84    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 11.56/1.84    inference(nnf_transformation,[],[f10])).
% 11.56/1.84  fof(f10,axiom,(
% 11.56/1.84    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 11.56/1.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 11.56/1.84  fof(f3423,plain,(
% 11.56/1.84    ( ! [X0] : (r2_hidden(sK2(k1_tarski(sK0),sK1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK0))) )),
% 11.56/1.84    inference(unit_resulting_resolution,[],[f85,f86,f3400,f179])).
% 11.56/1.84  fof(f179,plain,(
% 11.56/1.84    ( ! [X4,X2,X5,X3] : (~r1_tarski(X3,X5) | r1_tarski(X2,X4) | r2_hidden(sK2(X2,X4),X5) | ~r1_tarski(X2,X3)) )),
% 11.56/1.84    inference(resolution,[],[f127,f43])).
% 11.56/1.84  fof(f43,plain,(
% 11.56/1.84    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 11.56/1.84    inference(cnf_transformation,[],[f26])).
% 11.56/1.84  fof(f26,plain,(
% 11.56/1.84    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.56/1.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 11.56/1.84  fof(f25,plain,(
% 11.56/1.84    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 11.56/1.84    introduced(choice_axiom,[])).
% 11.56/1.84  fof(f24,plain,(
% 11.56/1.84    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.56/1.84    inference(rectify,[],[f23])).
% 11.56/1.84  fof(f23,plain,(
% 11.56/1.84    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.56/1.84    inference(nnf_transformation,[],[f19])).
% 11.56/1.84  fof(f19,plain,(
% 11.56/1.84    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.56/1.84    inference(ennf_transformation,[],[f1])).
% 11.56/1.84  fof(f1,axiom,(
% 11.56/1.84    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.56/1.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 11.56/1.84  fof(f127,plain,(
% 11.56/1.84    ( ! [X2,X3,X1] : (r2_hidden(sK2(X1,X2),X3) | ~r1_tarski(X1,X3) | r1_tarski(X1,X2)) )),
% 11.56/1.84    inference(resolution,[],[f43,f44])).
% 11.56/1.84  fof(f44,plain,(
% 11.56/1.84    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 11.56/1.84    inference(cnf_transformation,[],[f26])).
% 11.56/1.84  fof(f3400,plain,(
% 11.56/1.84    ~r1_tarski(k1_tarski(sK0),sK1)),
% 11.56/1.84    inference(unit_resulting_resolution,[],[f3200,f47])).
% 11.56/1.84  fof(f47,plain,(
% 11.56/1.84    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 11.56/1.84    inference(cnf_transformation,[],[f27])).
% 11.56/1.84  fof(f27,plain,(
% 11.56/1.84    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 11.56/1.84    inference(nnf_transformation,[],[f2])).
% 11.56/1.84  fof(f2,axiom,(
% 11.56/1.84    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 11.56/1.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 11.56/1.84  fof(f3200,plain,(
% 11.56/1.84    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 11.56/1.84    inference(backward_demodulation,[],[f3123,f3198])).
% 11.56/1.84  fof(f3198,plain,(
% 11.56/1.84    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)) )),
% 11.56/1.84    inference(forward_demodulation,[],[f3197,f97])).
% 11.56/1.84  fof(f97,plain,(
% 11.56/1.84    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 11.56/1.84    inference(unit_resulting_resolution,[],[f89,f47])).
% 11.56/1.84  fof(f89,plain,(
% 11.56/1.84    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 11.56/1.84    inference(superposition,[],[f38,f37])).
% 11.56/1.84  fof(f37,plain,(
% 11.56/1.84    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.56/1.84    inference(cnf_transformation,[],[f6])).
% 11.56/1.84  fof(f6,axiom,(
% 11.56/1.84    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.56/1.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 11.56/1.84  fof(f38,plain,(
% 11.56/1.84    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.56/1.84    inference(cnf_transformation,[],[f5])).
% 11.56/1.84  fof(f5,axiom,(
% 11.56/1.84    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.56/1.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 11.56/1.84  fof(f3197,plain,(
% 11.56/1.84    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) = k4_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X3,X2))) )),
% 11.56/1.84    inference(forward_demodulation,[],[f3196,f487])).
% 11.56/1.84  fof(f487,plain,(
% 11.56/1.84    ( ! [X4,X5] : (k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)) )),
% 11.56/1.84    inference(superposition,[],[f406,f406])).
% 11.56/1.84  fof(f406,plain,(
% 11.56/1.84    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 11.56/1.84    inference(unit_resulting_resolution,[],[f386,f135])).
% 11.56/1.84  fof(f135,plain,(
% 11.56/1.84    ( ! [X4,X3] : (k1_xboole_0 != k4_xboole_0(X3,k4_xboole_0(X3,X4)) | k4_xboole_0(X3,X4) = X3) )),
% 11.56/1.84    inference(superposition,[],[f42,f96])).
% 11.56/1.84  fof(f96,plain,(
% 11.56/1.84    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 11.56/1.84    inference(unit_resulting_resolution,[],[f38,f47])).
% 11.56/1.84  fof(f42,plain,(
% 11.56/1.84    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 11.56/1.84    inference(cnf_transformation,[],[f18])).
% 11.56/1.84  fof(f18,plain,(
% 11.56/1.84    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 11.56/1.84    inference(ennf_transformation,[],[f4])).
% 11.56/1.84  fof(f4,axiom,(
% 11.56/1.84    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 11.56/1.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 11.56/1.84  fof(f386,plain,(
% 11.56/1.84    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2)))) )),
% 11.56/1.84    inference(forward_demodulation,[],[f385,f96])).
% 11.56/1.84  fof(f385,plain,(
% 11.56/1.84    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2)))) )),
% 11.56/1.84    inference(forward_demodulation,[],[f345,f37])).
% 11.56/1.84  fof(f345,plain,(
% 11.56/1.84    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X2))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X2,k1_xboole_0))) )),
% 11.56/1.84    inference(superposition,[],[f66,f97])).
% 11.56/1.84  fof(f66,plain,(
% 11.56/1.84    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 11.56/1.84    inference(definition_unfolding,[],[f48,f40,f40,f40])).
% 11.56/1.84  fof(f40,plain,(
% 11.56/1.84    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.56/1.84    inference(cnf_transformation,[],[f8])).
% 11.56/1.84  fof(f8,axiom,(
% 11.56/1.84    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.56/1.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 11.56/1.84  fof(f48,plain,(
% 11.56/1.84    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 11.56/1.84    inference(cnf_transformation,[],[f9])).
% 11.56/1.84  fof(f9,axiom,(
% 11.56/1.84    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 11.56/1.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).
% 11.56/1.84  fof(f3196,plain,(
% 11.56/1.84    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(k4_xboole_0(X3,X2),X2)) = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)) )),
% 11.56/1.84    inference(forward_demodulation,[],[f2985,f37])).
% 11.56/1.84  fof(f2985,plain,(
% 11.56/1.84    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(k4_xboole_0(X3,X2),X2)) = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),k4_xboole_0(X2,k1_xboole_0))) )),
% 11.56/1.84    inference(superposition,[],[f67,f97])).
% 11.56/1.84  fof(f67,plain,(
% 11.56/1.84    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,X2),X1))) )),
% 11.56/1.84    inference(definition_unfolding,[],[f49,f40,f40,f40])).
% 11.56/1.84  fof(f49,plain,(
% 11.56/1.84    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)) )),
% 11.56/1.84    inference(cnf_transformation,[],[f3])).
% 11.56/1.84  fof(f3,axiom,(
% 11.56/1.84    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 11.56/1.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).
% 11.56/1.84  fof(f3123,plain,(
% 11.56/1.84    k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(sK0))),k1_tarski(sK0)) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 11.56/1.84    inference(backward_demodulation,[],[f131,f3122])).
% 11.56/1.84  fof(f3122,plain,(
% 11.56/1.84    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))) )),
% 11.56/1.84    inference(forward_demodulation,[],[f3121,f809])).
% 11.56/1.84  fof(f809,plain,(
% 11.56/1.84    ( ! [X54,X52,X53] : (k4_xboole_0(X53,X54) = k4_xboole_0(k4_xboole_0(X53,X54),k4_xboole_0(X52,X53))) )),
% 11.56/1.84    inference(superposition,[],[f406,f702])).
% 11.56/1.84  fof(f702,plain,(
% 11.56/1.84    ( ! [X8,X7,X9] : (k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X7,X9))) )),
% 11.56/1.84    inference(superposition,[],[f594,f406])).
% 11.56/1.84  fof(f594,plain,(
% 11.56/1.84    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0) )),
% 11.56/1.84    inference(unit_resulting_resolution,[],[f463,f135])).
% 11.56/1.84  fof(f463,plain,(
% 11.56/1.84    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X5,X4),X6)))) )),
% 11.56/1.84    inference(forward_demodulation,[],[f426,f106])).
% 11.56/1.84  fof(f106,plain,(
% 11.56/1.84    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 11.56/1.84    inference(unit_resulting_resolution,[],[f103,f47])).
% 11.56/1.84  fof(f103,plain,(
% 11.56/1.84    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 11.56/1.84    inference(superposition,[],[f38,f97])).
% 11.56/1.84  fof(f426,plain,(
% 11.56/1.84    ( ! [X6,X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X5,X4),X6))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X4,k4_xboole_0(X4,X6)))) )),
% 11.56/1.84    inference(superposition,[],[f66,f386])).
% 11.56/1.84  fof(f3121,plain,(
% 11.56/1.84    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),X2)) = k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))) )),
% 11.56/1.84    inference(forward_demodulation,[],[f2954,f37])).
% 11.56/1.84  fof(f2954,plain,(
% 11.56/1.84    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),X2)) = k4_xboole_0(k4_xboole_0(X2,k1_xboole_0),k4_xboole_0(X3,k4_xboole_0(X3,X2)))) )),
% 11.56/1.84    inference(superposition,[],[f67,f97])).
% 11.56/1.84  fof(f131,plain,(
% 11.56/1.84    k4_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(sK0)))) != k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(sK0))),k1_tarski(sK0))),
% 11.56/1.84    inference(unit_resulting_resolution,[],[f64,f42])).
% 11.56/1.84  fof(f64,plain,(
% 11.56/1.84    k1_tarski(sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(sK0)))),
% 11.56/1.84    inference(definition_unfolding,[],[f36,f40])).
% 11.56/1.84  fof(f36,plain,(
% 11.56/1.84    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))),
% 11.56/1.84    inference(cnf_transformation,[],[f22])).
% 11.56/1.84  fof(f86,plain,(
% 11.56/1.84    ( ! [X2,X1] : (r1_tarski(k1_tarski(X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 11.56/1.84    inference(equality_resolution,[],[f75])).
% 11.56/1.84  fof(f75,plain,(
% 11.56/1.84    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k1_tarski(X2) != X0) )),
% 11.56/1.84    inference(definition_unfolding,[],[f59,f63])).
% 11.56/1.84  fof(f59,plain,(
% 11.56/1.84    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 11.56/1.84    inference(cnf_transformation,[],[f34])).
% 11.56/1.84  fof(f34,plain,(
% 11.56/1.84    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 11.56/1.84    inference(flattening,[],[f33])).
% 11.56/1.84  fof(f33,plain,(
% 11.56/1.84    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 11.56/1.84    inference(nnf_transformation,[],[f20])).
% 11.56/1.84  fof(f20,plain,(
% 11.56/1.84    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 11.56/1.84    inference(ennf_transformation,[],[f14])).
% 11.56/1.84  fof(f14,axiom,(
% 11.56/1.84    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 11.56/1.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_zfmisc_1)).
% 11.56/1.84  fof(f85,plain,(
% 11.56/1.84    ( ! [X2,X1] : (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 11.56/1.84    inference(equality_resolution,[],[f74])).
% 11.56/1.84  fof(f74,plain,(
% 11.56/1.84    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) != X0) )),
% 11.56/1.84    inference(definition_unfolding,[],[f60,f63,f63])).
% 11.56/1.84  fof(f60,plain,(
% 11.56/1.84    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X2) != X0) )),
% 11.56/1.84    inference(cnf_transformation,[],[f34])).
% 11.56/1.84  fof(f3410,plain,(
% 11.56/1.84    ~r2_hidden(sK2(k1_tarski(sK0),sK1),sK1)),
% 11.56/1.84    inference(unit_resulting_resolution,[],[f3400,f45])).
% 11.56/1.84  fof(f45,plain,(
% 11.56/1.84    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 11.56/1.84    inference(cnf_transformation,[],[f26])).
% 11.56/1.84  % SZS output end Proof for theBenchmark
% 11.56/1.84  % (18241)------------------------------
% 11.56/1.84  % (18241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.56/1.84  % (18241)Termination reason: Refutation
% 11.56/1.84  
% 11.56/1.84  % (18241)Memory used [KB]: 14583
% 11.56/1.84  % (18241)Time elapsed: 0.873 s
% 11.56/1.84  % (18241)------------------------------
% 11.56/1.84  % (18241)------------------------------
% 11.56/1.84  % (18183)Success in time 1.475 s
%------------------------------------------------------------------------------
