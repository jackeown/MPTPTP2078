%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:15 EST 2020

% Result     : Theorem 11.50s
% Output     : Refutation 11.50s
% Verified   : 
% Statistics : Number of formulae       :  163 (34187 expanded)
%              Number of leaves         :   24 (9812 expanded)
%              Depth                    :   32
%              Number of atoms          :  328 (107947 expanded)
%              Number of equality atoms :  143 (33869 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19757,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19686,f7156])).

fof(f7156,plain,(
    ~ r2_hidden(sK5(k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1),sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f5205,f88])).

fof(f88,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k4_enumset1(X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k4_enumset1(X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f58,f77])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f5205,plain,(
    sK0 != sK5(k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f79,f78,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X1
      | k1_xboole_0 = X0
      | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f63,f77])).

fof(f63,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sK5(X0,X1) != X1
        & r2_hidden(sK5(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK5(X0,X1) != X1
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f78,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f46,f77,f77])).

fof(f46,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
        & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f79,plain,(
    k1_xboole_0 != k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f45,f77])).

fof(f45,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f19686,plain,(
    r2_hidden(sK5(k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1),sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f5665,f11049])).

fof(f11049,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X7,k4_xboole_0(X5,X6))
      | r2_hidden(X7,X5) ) ),
    inference(subsumption_resolution,[],[f11018,f6096])).

fof(f6096,plain,(
    ! [X17,X18,X16] :
      ( ~ r2_hidden(X18,k4_xboole_0(X16,X17))
      | ~ r2_hidden(X18,k3_xboole_0(X16,X17)) ) ),
    inference(superposition,[],[f90,f4780])).

fof(f4780,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k3_xboole_0(X2,X3)) = k4_xboole_0(X2,X3) ),
    inference(backward_demodulation,[],[f2709,f4639])).

fof(f4639,plain,(
    ! [X15] : k2_xboole_0(k1_xboole_0,X15) = X15 ),
    inference(backward_demodulation,[],[f749,f4637])).

fof(f4637,plain,(
    ! [X16] : k4_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(backward_demodulation,[],[f4576,f4590])).

fof(f4590,plain,(
    ! [X0] : k4_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(superposition,[],[f4587,f51])).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f4587,plain,(
    ! [X16] : k4_xboole_0(k5_xboole_0(k1_xboole_0,X16),k1_xboole_0) = X16 ),
    inference(forward_demodulation,[],[f4586,f749])).

fof(f4586,plain,(
    ! [X16] : k4_xboole_0(k5_xboole_0(k1_xboole_0,X16),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X16,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f4548,f1302])).

fof(f1302,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f773,f1101])).

fof(f1101,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f941,f1061])).

fof(f1061,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X1)) ),
    inference(unit_resulting_resolution,[],[f169,f992,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f992,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f87,f751,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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

fof(f751,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f747,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f747,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(superposition,[],[f89,f111])).

fof(f111,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,k4_xboole_0(X0,X0))) = X1 ),
    inference(unit_resulting_resolution,[],[f103,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f103,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f50,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f64,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f64,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f87,plain,(
    ! [X3] : r2_hidden(X3,k4_enumset1(X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k4_enumset1(X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k4_enumset1(X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f59,f77])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f169,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,X2))) ),
    inference(unit_resulting_resolution,[],[f128,f128,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f128,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(unit_resulting_resolution,[],[f87,f117,f54])).

fof(f117,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f105,f71])).

fof(f105,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f89,f69])).

fof(f941,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,X0) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,X2)) ),
    inference(unit_resulting_resolution,[],[f125,f169,f56])).

fof(f125,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,X1)) ),
    inference(unit_resulting_resolution,[],[f87,f109,f54])).

fof(f109,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f103,f71])).

fof(f773,plain,(
    ! [X0,X1] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X1,X1) ),
    inference(unit_resulting_resolution,[],[f125,f128,f56])).

fof(f4548,plain,(
    ! [X16] : k4_xboole_0(k5_xboole_0(k1_xboole_0,X16),k1_xboole_0) = k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(X16,k1_xboole_0)),k4_xboole_0(X16,k1_xboole_0)) ),
    inference(superposition,[],[f68,f2599])).

fof(f2599,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f749,f1302])).

fof(f68,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_xboole_1)).

fof(f4576,plain,(
    ! [X16] : k4_xboole_0(X16,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X16,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f4575,f4016])).

fof(f4016,plain,(
    ! [X12] : k4_xboole_0(X12,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X12,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f4015,f1984])).

fof(f1984,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1624,f1302])).

fof(f1624,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(backward_demodulation,[],[f1061,f1302])).

fof(f4015,plain,(
    ! [X12] : k4_xboole_0(X12,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X12,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3987,f47])).

fof(f3987,plain,(
    ! [X12] : k4_xboole_0(X12,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X12,k1_xboole_0),k3_xboole_0(k3_xboole_0(X12,k1_xboole_0),k1_xboole_0)) ),
    inference(superposition,[],[f67,f2599])).

fof(f67,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_xboole_1)).

fof(f4575,plain,(
    ! [X16] : k2_xboole_0(k4_xboole_0(X16,k1_xboole_0),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X16,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f4532,f1302])).

fof(f4532,plain,(
    ! [X16] : k4_xboole_0(k5_xboole_0(X16,k1_xboole_0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X16,k1_xboole_0),k4_xboole_0(k1_xboole_0,k2_xboole_0(X16,k1_xboole_0))) ),
    inference(superposition,[],[f68,f2599])).

fof(f749,plain,(
    ! [X15] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X15,k1_xboole_0)) = X15 ),
    inference(superposition,[],[f99,f111])).

fof(f99,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f89,f55])).

fof(f2709,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k3_xboole_0(X2,X3)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f65,f1101])).

fof(f65,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X2,X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f54,f49])).

fof(f49,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f11018,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X7,k4_xboole_0(X5,X6))
      | r2_hidden(X7,X5)
      | r2_hidden(X7,k3_xboole_0(X5,X6)) ) ),
    inference(superposition,[],[f72,f10593])).

fof(f10593,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f10592,f4684])).

fof(f4684,plain,(
    ! [X12] : k2_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(backward_demodulation,[],[f4016,f4637])).

fof(f10592,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f10591,f1101])).

fof(f10591,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f10590,f4845])).

fof(f4845,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f4691,f4639])).

fof(f4691,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = X0 ),
    inference(backward_demodulation,[],[f4068,f4637])).

fof(f4068,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k3_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1),k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1))) ),
    inference(forward_demodulation,[],[f4055,f2709])).

fof(f4055,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k3_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1),k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k3_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1))) ),
    inference(unit_resulting_resolution,[],[f4036,f55])).

fof(f4036,plain,(
    ! [X4,X3] : r1_tarski(k3_xboole_0(k4_xboole_0(X3,k1_xboole_0),X4),k4_xboole_0(X3,k1_xboole_0)) ),
    inference(superposition,[],[f64,f4016])).

fof(f10590,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)))) ),
    inference(forward_demodulation,[],[f10550,f7705])).

fof(f7705,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k5_xboole_0(X3,k3_xboole_0(X3,X4)),X5) = k4_xboole_0(X3,k2_xboole_0(k3_xboole_0(X3,X4),X5)) ),
    inference(forward_demodulation,[],[f7653,f4684])).

fof(f7653,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k5_xboole_0(X3,k3_xboole_0(X3,X4)),X5) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(k3_xboole_0(X3,X4),X5)),k1_xboole_0) ),
    inference(superposition,[],[f68,f5902])).

fof(f5902,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(unit_resulting_resolution,[],[f64,f5416])).

fof(f5416,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f4841,f4650])).

fof(f4650,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k1_xboole_0)
      | k1_xboole_0 = X8 ) ),
    inference(backward_demodulation,[],[f2675,f4637])).

fof(f2675,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k1_xboole_0)
      | k1_xboole_0 = k4_xboole_0(X8,k1_xboole_0) ) ),
    inference(resolution,[],[f2668,f1905])).

fof(f1905,plain,(
    ! [X8] :
      ( r2_hidden(sK3(X8,k1_xboole_0),X8)
      | k1_xboole_0 = X8 ) ),
    inference(forward_demodulation,[],[f1867,f1792])).

fof(f1792,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_xboole_0,X2),X3) ),
    inference(backward_demodulation,[],[f831,f1601])).

fof(f1601,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X1,X2),X1) ),
    inference(backward_demodulation,[],[f788,f1302])).

fof(f788,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k3_xboole_0(X1,X2),X1) ),
    inference(unit_resulting_resolution,[],[f128,f162,f56])).

fof(f162,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k4_xboole_0(k3_xboole_0(X1,X2),X1)) ),
    inference(unit_resulting_resolution,[],[f87,f145,f54])).

fof(f145,plain,(
    ! [X2,X0,X1] : r1_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X0),X2) ),
    inference(unit_resulting_resolution,[],[f104,f71])).

fof(f104,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(k3_xboole_0(X0,X1),X0),X2) ),
    inference(unit_resulting_resolution,[],[f64,f69])).

fof(f831,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X0) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X2),X3) ),
    inference(unit_resulting_resolution,[],[f162,f639,f56])).

fof(f639,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k4_xboole_0(k3_xboole_0(k1_xboole_0,X1),X2)) ),
    inference(unit_resulting_resolution,[],[f87,f630,f54])).

fof(f630,plain,(
    ! [X2,X0,X1] : r1_xboole_0(k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1),X2) ),
    inference(unit_resulting_resolution,[],[f623,f71])).

fof(f623,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1),X2) ),
    inference(unit_resulting_resolution,[],[f621,f69])).

fof(f621,plain,(
    ! [X10,X8,X9] : r1_tarski(k3_xboole_0(k1_xboole_0,X10),k2_xboole_0(X8,X9)) ),
    inference(superposition,[],[f64,f99])).

fof(f1867,plain,(
    ! [X10,X8,X9] :
      ( r2_hidden(sK3(X8,k1_xboole_0),X8)
      | k4_xboole_0(k3_xboole_0(k1_xboole_0,X9),X10) = X8 ) ),
    inference(backward_demodulation,[],[f958,f1792])).

fof(f958,plain,(
    ! [X10,X8,X9] :
      ( r2_hidden(sK3(X8,k4_xboole_0(k3_xboole_0(k1_xboole_0,X9),X10)),X8)
      | k4_xboole_0(k3_xboole_0(k1_xboole_0,X9),X10) = X8 ) ),
    inference(resolution,[],[f56,f639])).

fof(f2668,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,k1_xboole_0))
      | ~ r1_tarski(X1,k1_xboole_0) ) ),
    inference(condensation,[],[f2664])).

fof(f2664,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,k4_xboole_0(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f2645,f54])).

fof(f2645,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(k4_xboole_0(X2,k1_xboole_0),X3)
      | ~ r1_tarski(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f2610,f2511])).

fof(f2511,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | r1_xboole_0(X3,X2) ) ),
    inference(superposition,[],[f71,f1302])).

fof(f2610,plain,(
    ! [X1] :
      ( r1_tarski(k4_xboole_0(X1,k1_xboole_0),k1_xboole_0)
      | ~ r1_tarski(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f69,f2599])).

fof(f4841,plain,(
    ! [X8,X7] :
      ( r1_tarski(k4_xboole_0(X8,X7),k1_xboole_0)
      | ~ r1_tarski(X8,X7) ) ),
    inference(forward_demodulation,[],[f4687,f4637])).

fof(f4687,plain,(
    ! [X8,X7] :
      ( ~ r1_tarski(X8,X7)
      | r1_tarski(k4_xboole_0(X8,k4_xboole_0(X7,k1_xboole_0)),k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f4038,f4637])).

fof(f4038,plain,(
    ! [X8,X7] :
      ( ~ r1_tarski(X8,k4_xboole_0(X7,k1_xboole_0))
      | r1_tarski(k4_xboole_0(X8,k4_xboole_0(X7,k1_xboole_0)),k1_xboole_0) ) ),
    inference(superposition,[],[f69,f4016])).

fof(f10550,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f10162,f55])).

fof(f10162,plain,(
    ! [X24,X25] : r1_tarski(k4_xboole_0(X24,X25),k5_xboole_0(X24,k3_xboole_0(X24,X25))) ),
    inference(superposition,[],[f10104,f4780])).

fof(f10104,plain,(
    ! [X35,X36] : r1_tarski(k4_xboole_0(X36,X35),k5_xboole_0(X36,X35)) ),
    inference(forward_demodulation,[],[f10066,f4637])).

fof(f10066,plain,(
    ! [X35,X36] : r1_tarski(k4_xboole_0(X36,X35),k4_xboole_0(k5_xboole_0(X36,X35),k1_xboole_0)) ),
    inference(superposition,[],[f4561,f4684])).

fof(f4561,plain,(
    ! [X4,X2,X3] : r1_tarski(k4_xboole_0(X2,k2_xboole_0(X3,X4)),k4_xboole_0(k5_xboole_0(X2,X3),X4)) ),
    inference(superposition,[],[f50,f68])).

fof(f5665,plain,(
    r2_hidden(sK5(k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1),sK0),k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f79,f78,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | k1_xboole_0 = X0
      | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f62,f77])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:32:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (24039)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (24057)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (24055)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (24047)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (24048)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (24042)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (24048)Refutation not found, incomplete strategy% (24048)------------------------------
% 0.21/0.51  % (24048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24048)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24048)Memory used [KB]: 10618
% 0.21/0.51  % (24048)Time elapsed: 0.080 s
% 0.21/0.51  % (24048)------------------------------
% 0.21/0.51  % (24048)------------------------------
% 0.21/0.52  % (24056)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (24065)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (24043)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (24040)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (24054)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (24064)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (24050)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (24059)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (24046)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (24067)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (24038)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (24051)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (24046)Refutation not found, incomplete strategy% (24046)------------------------------
% 0.21/0.54  % (24046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24046)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24046)Memory used [KB]: 10618
% 0.21/0.54  % (24046)Time elapsed: 0.131 s
% 0.21/0.54  % (24046)------------------------------
% 0.21/0.54  % (24046)------------------------------
% 0.21/0.55  % (24049)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (24044)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (24068)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (24040)Refutation not found, incomplete strategy% (24040)------------------------------
% 0.21/0.55  % (24040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24040)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24040)Memory used [KB]: 10618
% 0.21/0.55  % (24040)Time elapsed: 0.142 s
% 0.21/0.55  % (24040)------------------------------
% 0.21/0.55  % (24040)------------------------------
% 0.21/0.55  % (24052)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (24060)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (24059)Refutation not found, incomplete strategy% (24059)------------------------------
% 0.21/0.55  % (24059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24059)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24059)Memory used [KB]: 10746
% 0.21/0.55  % (24059)Time elapsed: 0.137 s
% 0.21/0.55  % (24059)------------------------------
% 0.21/0.55  % (24059)------------------------------
% 0.21/0.56  % (24060)Refutation not found, incomplete strategy% (24060)------------------------------
% 0.21/0.56  % (24060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24060)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (24060)Memory used [KB]: 1663
% 0.21/0.56  % (24060)Time elapsed: 0.149 s
% 0.21/0.56  % (24060)------------------------------
% 0.21/0.56  % (24060)------------------------------
% 0.21/0.56  % (24066)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (24053)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (24061)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (24069)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (24062)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.57  % (24041)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.58  % (24045)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 2.08/0.65  % (24091)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.08/0.68  % (24092)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.08/0.68  % (24093)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.08/0.69  % (24095)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.08/0.69  % (24049)Refutation not found, incomplete strategy% (24049)------------------------------
% 2.08/0.69  % (24049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.69  % (24049)Termination reason: Refutation not found, incomplete strategy
% 2.08/0.69  
% 2.08/0.69  % (24049)Memory used [KB]: 11385
% 2.08/0.69  % (24049)Time elapsed: 0.254 s
% 2.08/0.69  % (24049)------------------------------
% 2.08/0.69  % (24049)------------------------------
% 2.08/0.70  % (24094)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 3.16/0.82  % (24043)Time limit reached!
% 3.16/0.82  % (24043)------------------------------
% 3.16/0.82  % (24043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.16/0.82  % (24043)Termination reason: Time limit
% 3.16/0.82  % (24043)Termination phase: Saturation
% 3.16/0.82  
% 3.16/0.82  % (24043)Memory used [KB]: 10362
% 3.16/0.82  % (24043)Time elapsed: 0.403 s
% 3.16/0.82  % (24043)------------------------------
% 3.16/0.82  % (24043)------------------------------
% 3.16/0.83  % (24096)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.09/0.91  % (24050)Time limit reached!
% 4.09/0.91  % (24050)------------------------------
% 4.09/0.91  % (24050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.91  % (24050)Termination reason: Time limit
% 4.09/0.91  % (24050)Termination phase: Saturation
% 4.09/0.91  
% 4.09/0.91  % (24050)Memory used [KB]: 9338
% 4.09/0.91  % (24050)Time elapsed: 0.500 s
% 4.09/0.91  % (24050)------------------------------
% 4.09/0.91  % (24050)------------------------------
% 4.09/0.91  % (24038)Time limit reached!
% 4.09/0.91  % (24038)------------------------------
% 4.09/0.91  % (24038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.91  % (24038)Termination reason: Time limit
% 4.09/0.91  
% 4.09/0.91  % (24038)Memory used [KB]: 2814
% 4.09/0.91  % (24038)Time elapsed: 0.506 s
% 4.09/0.91  % (24038)------------------------------
% 4.09/0.91  % (24038)------------------------------
% 4.31/0.93  % (24039)Time limit reached!
% 4.31/0.93  % (24039)------------------------------
% 4.31/0.93  % (24039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.93  % (24039)Termination reason: Time limit
% 4.31/0.93  % (24039)Termination phase: Saturation
% 4.31/0.93  
% 4.31/0.93  % (24039)Memory used [KB]: 10106
% 4.31/0.93  % (24039)Time elapsed: 0.500 s
% 4.31/0.93  % (24039)------------------------------
% 4.31/0.93  % (24039)------------------------------
% 4.31/0.94  % (24097)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.31/0.96  % (24055)Time limit reached!
% 4.31/0.96  % (24055)------------------------------
% 4.31/0.96  % (24055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.96  % (24055)Termination reason: Time limit
% 4.31/0.96  
% 4.31/0.96  % (24055)Memory used [KB]: 13304
% 4.31/0.96  % (24055)Time elapsed: 0.527 s
% 4.31/0.96  % (24055)------------------------------
% 4.31/0.96  % (24055)------------------------------
% 4.31/0.99  % (24094)Time limit reached!
% 4.31/0.99  % (24094)------------------------------
% 4.31/0.99  % (24094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.99  % (24094)Termination reason: Time limit
% 4.31/0.99  
% 4.31/0.99  % (24094)Memory used [KB]: 8315
% 4.31/0.99  % (24094)Time elapsed: 0.408 s
% 4.31/0.99  % (24094)------------------------------
% 4.31/0.99  % (24094)------------------------------
% 4.85/1.01  % (24095)Time limit reached!
% 4.85/1.01  % (24095)------------------------------
% 4.85/1.01  % (24095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.85/1.01  % (24095)Termination reason: Time limit
% 4.85/1.01  % (24095)Termination phase: Saturation
% 4.85/1.01  
% 4.85/1.01  % (24095)Memory used [KB]: 15351
% 4.85/1.01  % (24095)Time elapsed: 0.400 s
% 4.85/1.01  % (24095)------------------------------
% 4.85/1.01  % (24095)------------------------------
% 4.85/1.02  % (24045)Time limit reached!
% 4.85/1.02  % (24045)------------------------------
% 4.85/1.02  % (24045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.85/1.02  % (24045)Termination reason: Time limit
% 4.85/1.02  
% 4.85/1.02  % (24045)Memory used [KB]: 10874
% 4.85/1.02  % (24045)Time elapsed: 0.618 s
% 4.85/1.02  % (24045)------------------------------
% 4.85/1.02  % (24045)------------------------------
% 4.85/1.02  % (24098)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.85/1.03  % (24054)Time limit reached!
% 4.85/1.03  % (24054)------------------------------
% 4.85/1.03  % (24054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.85/1.03  % (24054)Termination reason: Time limit
% 4.85/1.03  
% 4.85/1.03  % (24054)Memory used [KB]: 17014
% 4.85/1.03  % (24054)Time elapsed: 0.606 s
% 4.85/1.03  % (24054)------------------------------
% 4.85/1.03  % (24054)------------------------------
% 4.85/1.03  % (24068)Time limit reached!
% 4.85/1.03  % (24068)------------------------------
% 4.85/1.03  % (24068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.85/1.03  % (24068)Termination reason: Time limit
% 4.85/1.03  
% 4.85/1.03  % (24068)Memory used [KB]: 10106
% 4.85/1.03  % (24068)Time elapsed: 0.625 s
% 4.85/1.03  % (24068)------------------------------
% 4.85/1.03  % (24068)------------------------------
% 4.85/1.05  % (24100)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 4.85/1.06  % (24099)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 4.85/1.07  % (24108)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 5.61/1.09  % (24108)Refutation not found, incomplete strategy% (24108)------------------------------
% 5.61/1.09  % (24108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.61/1.09  % (24108)Termination reason: Refutation not found, incomplete strategy
% 5.61/1.09  
% 5.61/1.09  % (24108)Memory used [KB]: 6268
% 5.61/1.09  % (24108)Time elapsed: 0.115 s
% 5.61/1.09  % (24108)------------------------------
% 5.61/1.09  % (24108)------------------------------
% 5.61/1.12  % (24124)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 5.61/1.12  % (24140)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 5.61/1.12  % (24140)Refutation not found, incomplete strategy% (24140)------------------------------
% 5.61/1.12  % (24140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.61/1.13  % (24140)Termination reason: Refutation not found, incomplete strategy
% 5.61/1.13  
% 5.61/1.13  % (24140)Memory used [KB]: 1663
% 5.61/1.13  % (24140)Time elapsed: 0.057 s
% 5.61/1.13  % (24140)------------------------------
% 5.61/1.13  % (24140)------------------------------
% 5.61/1.13  % (24124)Refutation not found, incomplete strategy% (24124)------------------------------
% 5.61/1.13  % (24124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.61/1.13  % (24124)Termination reason: Refutation not found, incomplete strategy
% 5.61/1.13  
% 5.61/1.13  % (24124)Memory used [KB]: 1791
% 5.61/1.13  % (24124)Time elapsed: 0.109 s
% 5.61/1.13  % (24124)------------------------------
% 5.61/1.13  % (24124)------------------------------
% 5.61/1.13  % (24136)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 5.61/1.15  % (24145)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 5.61/1.18  % (24153)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 6.60/1.21  % (24166)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 6.75/1.26  % (24193)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 6.75/1.26  % (24191)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 8.73/1.51  % (24166)Time limit reached!
% 8.73/1.51  % (24166)------------------------------
% 8.73/1.51  % (24166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.73/1.51  % (24166)Termination reason: Time limit
% 8.73/1.51  % (24166)Termination phase: Saturation
% 8.73/1.51  
% 8.73/1.51  % (24166)Memory used [KB]: 4477
% 8.73/1.51  % (24166)Time elapsed: 0.400 s
% 8.73/1.51  % (24166)------------------------------
% 8.73/1.51  % (24166)------------------------------
% 9.01/1.54  % (24136)Time limit reached!
% 9.01/1.54  % (24136)------------------------------
% 9.01/1.54  % (24136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.01/1.54  % (24136)Termination reason: Time limit
% 9.01/1.54  % (24136)Termination phase: Saturation
% 9.01/1.54  
% 9.01/1.54  % (24136)Memory used [KB]: 7036
% 9.01/1.54  % (24136)Time elapsed: 0.500 s
% 9.01/1.54  % (24136)------------------------------
% 9.01/1.54  % (24136)------------------------------
% 9.01/1.60  % (24066)Time limit reached!
% 9.01/1.60  % (24066)------------------------------
% 9.01/1.60  % (24066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.01/1.60  % (24066)Termination reason: Time limit
% 9.01/1.60  % (24066)Termination phase: Saturation
% 9.01/1.60  
% 9.01/1.60  % (24066)Memory used [KB]: 15479
% 9.01/1.60  % (24066)Time elapsed: 1.200 s
% 9.01/1.60  % (24066)------------------------------
% 9.01/1.60  % (24066)------------------------------
% 9.01/1.62  % (24061)Time limit reached!
% 9.01/1.62  % (24061)------------------------------
% 9.01/1.62  % (24061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.01/1.62  % (24061)Termination reason: Time limit
% 9.01/1.62  
% 9.01/1.62  % (24061)Memory used [KB]: 15735
% 9.01/1.62  % (24061)Time elapsed: 1.208 s
% 9.01/1.62  % (24061)------------------------------
% 9.01/1.62  % (24061)------------------------------
% 9.67/1.63  % (24331)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 9.67/1.69  % (24339)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 10.59/1.72  % (24064)Time limit reached!
% 10.59/1.72  % (24064)------------------------------
% 10.59/1.72  % (24064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.59/1.72  % (24064)Termination reason: Time limit
% 10.59/1.72  
% 10.59/1.72  % (24064)Memory used [KB]: 17654
% 10.59/1.72  % (24064)Time elapsed: 1.320 s
% 10.59/1.72  % (24064)------------------------------
% 10.59/1.72  % (24064)------------------------------
% 10.59/1.73  % (24053)Time limit reached!
% 10.59/1.73  % (24053)------------------------------
% 10.59/1.73  % (24053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.59/1.73  % (24053)Termination reason: Time limit
% 10.59/1.73  % (24053)Termination phase: Saturation
% 10.59/1.73  
% 10.59/1.73  % (24053)Memory used [KB]: 9722
% 10.59/1.73  % (24053)Time elapsed: 1.300 s
% 10.59/1.73  % (24053)------------------------------
% 10.59/1.73  % (24053)------------------------------
% 10.59/1.74  % (24340)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 10.59/1.75  % (24341)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 11.50/1.83  % (24343)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 11.50/1.85  % (24342)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 11.50/1.85  % (24098)Refutation found. Thanks to Tanya!
% 11.50/1.85  % SZS status Theorem for theBenchmark
% 11.50/1.85  % SZS output start Proof for theBenchmark
% 11.50/1.85  fof(f19757,plain,(
% 11.50/1.85    $false),
% 11.50/1.85    inference(subsumption_resolution,[],[f19686,f7156])).
% 11.50/1.85  fof(f7156,plain,(
% 11.50/1.85    ~r2_hidden(sK5(k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1),sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f5205,f88])).
% 11.50/1.85  fof(f88,plain,(
% 11.50/1.85    ( ! [X0,X3] : (~r2_hidden(X3,k4_enumset1(X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 11.50/1.85    inference(equality_resolution,[],[f83])).
% 11.50/1.85  fof(f83,plain,(
% 11.50/1.85    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k4_enumset1(X0,X0,X0,X0,X0,X0) != X1) )),
% 11.50/1.85    inference(definition_unfolding,[],[f58,f77])).
% 11.50/1.85  fof(f77,plain,(
% 11.50/1.85    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 11.50/1.85    inference(definition_unfolding,[],[f48,f76])).
% 11.50/1.85  fof(f76,plain,(
% 11.50/1.85    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 11.50/1.85    inference(cnf_transformation,[],[f17])).
% 11.50/1.85  fof(f17,axiom,(
% 11.50/1.85    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 11.50/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).
% 11.50/1.85  fof(f48,plain,(
% 11.50/1.85    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 11.50/1.85    inference(cnf_transformation,[],[f18])).
% 11.50/1.85  fof(f18,axiom,(
% 11.50/1.85    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)),
% 11.50/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).
% 11.50/1.85  fof(f58,plain,(
% 11.50/1.85    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 11.50/1.85    inference(cnf_transformation,[],[f41])).
% 11.50/1.85  fof(f41,plain,(
% 11.50/1.85    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.50/1.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).
% 11.50/1.85  fof(f40,plain,(
% 11.50/1.85    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 11.50/1.85    introduced(choice_axiom,[])).
% 11.50/1.85  fof(f39,plain,(
% 11.50/1.85    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.50/1.85    inference(rectify,[],[f38])).
% 11.50/1.85  fof(f38,plain,(
% 11.50/1.85    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 11.50/1.85    inference(nnf_transformation,[],[f16])).
% 11.50/1.85  fof(f16,axiom,(
% 11.50/1.85    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 11.50/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 11.50/1.85  fof(f5205,plain,(
% 11.50/1.85    sK0 != sK5(k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1),sK0)),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f79,f78,f84])).
% 11.50/1.85  fof(f84,plain,(
% 11.50/1.85    ( ! [X0,X1] : (sK5(X0,X1) != X1 | k1_xboole_0 = X0 | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0) )),
% 11.50/1.85    inference(definition_unfolding,[],[f63,f77])).
% 11.50/1.85  fof(f63,plain,(
% 11.50/1.85    ( ! [X0,X1] : (sK5(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 11.50/1.85    inference(cnf_transformation,[],[f43])).
% 11.50/1.85  fof(f43,plain,(
% 11.50/1.85    ! [X0,X1] : ((sK5(X0,X1) != X1 & r2_hidden(sK5(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 11.50/1.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f42])).
% 11.50/1.85  fof(f42,plain,(
% 11.50/1.85    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK5(X0,X1) != X1 & r2_hidden(sK5(X0,X1),X0)))),
% 11.50/1.85    introduced(choice_axiom,[])).
% 11.50/1.85  fof(f27,plain,(
% 11.50/1.85    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 11.50/1.85    inference(ennf_transformation,[],[f19])).
% 11.50/1.85  fof(f19,axiom,(
% 11.50/1.85    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 11.50/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 11.50/1.85  fof(f78,plain,(
% 11.50/1.85    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 11.50/1.85    inference(definition_unfolding,[],[f46,f77,f77])).
% 11.50/1.85  fof(f46,plain,(
% 11.50/1.85    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 11.50/1.85    inference(cnf_transformation,[],[f32])).
% 11.50/1.85  fof(f32,plain,(
% 11.50/1.85    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 11.50/1.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f31])).
% 11.50/1.85  fof(f31,plain,(
% 11.50/1.85    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1))),
% 11.50/1.85    introduced(choice_axiom,[])).
% 11.50/1.85  fof(f23,plain,(
% 11.50/1.85    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1))),
% 11.50/1.85    inference(ennf_transformation,[],[f21])).
% 11.50/1.85  fof(f21,negated_conjecture,(
% 11.50/1.85    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 11.50/1.85    inference(negated_conjecture,[],[f20])).
% 11.50/1.85  fof(f20,conjecture,(
% 11.50/1.85    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 11.50/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 11.50/1.85  fof(f79,plain,(
% 11.50/1.85    k1_xboole_0 != k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 11.50/1.85    inference(definition_unfolding,[],[f45,f77])).
% 11.50/1.85  fof(f45,plain,(
% 11.50/1.85    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 11.50/1.85    inference(cnf_transformation,[],[f32])).
% 11.50/1.85  fof(f19686,plain,(
% 11.50/1.85    r2_hidden(sK5(k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1),sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f5665,f11049])).
% 11.50/1.85  fof(f11049,plain,(
% 11.50/1.85    ( ! [X6,X7,X5] : (~r2_hidden(X7,k4_xboole_0(X5,X6)) | r2_hidden(X7,X5)) )),
% 11.50/1.85    inference(subsumption_resolution,[],[f11018,f6096])).
% 11.50/1.85  fof(f6096,plain,(
% 11.50/1.85    ( ! [X17,X18,X16] : (~r2_hidden(X18,k4_xboole_0(X16,X17)) | ~r2_hidden(X18,k3_xboole_0(X16,X17))) )),
% 11.50/1.85    inference(superposition,[],[f90,f4780])).
% 11.50/1.85  fof(f4780,plain,(
% 11.50/1.85    ( ! [X2,X3] : (k4_xboole_0(X2,k3_xboole_0(X2,X3)) = k4_xboole_0(X2,X3)) )),
% 11.50/1.85    inference(backward_demodulation,[],[f2709,f4639])).
% 11.50/1.85  fof(f4639,plain,(
% 11.50/1.85    ( ! [X15] : (k2_xboole_0(k1_xboole_0,X15) = X15) )),
% 11.50/1.85    inference(backward_demodulation,[],[f749,f4637])).
% 11.50/1.85  fof(f4637,plain,(
% 11.50/1.85    ( ! [X16] : (k4_xboole_0(X16,k1_xboole_0) = X16) )),
% 11.50/1.85    inference(backward_demodulation,[],[f4576,f4590])).
% 11.50/1.85  fof(f4590,plain,(
% 11.50/1.85    ( ! [X0] : (k4_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0) )),
% 11.50/1.85    inference(superposition,[],[f4587,f51])).
% 11.50/1.85  fof(f51,plain,(
% 11.50/1.85    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 11.50/1.85    inference(cnf_transformation,[],[f1])).
% 11.50/1.85  fof(f1,axiom,(
% 11.50/1.85    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 11.50/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 11.50/1.85  fof(f4587,plain,(
% 11.50/1.85    ( ! [X16] : (k4_xboole_0(k5_xboole_0(k1_xboole_0,X16),k1_xboole_0) = X16) )),
% 11.50/1.85    inference(forward_demodulation,[],[f4586,f749])).
% 11.50/1.85  fof(f4586,plain,(
% 11.50/1.85    ( ! [X16] : (k4_xboole_0(k5_xboole_0(k1_xboole_0,X16),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X16,k1_xboole_0))) )),
% 11.50/1.85    inference(forward_demodulation,[],[f4548,f1302])).
% 11.50/1.85  fof(f1302,plain,(
% 11.50/1.85    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 11.50/1.85    inference(backward_demodulation,[],[f773,f1101])).
% 11.50/1.85  fof(f1101,plain,(
% 11.50/1.85    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 11.50/1.85    inference(backward_demodulation,[],[f941,f1061])).
% 11.50/1.85  fof(f1061,plain,(
% 11.50/1.85    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X1))) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f169,f992,f56])).
% 11.50/1.85  fof(f56,plain,(
% 11.50/1.85    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0) | X0 = X1) )),
% 11.50/1.85    inference(cnf_transformation,[],[f37])).
% 11.50/1.85  fof(f37,plain,(
% 11.50/1.85    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 11.50/1.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 11.50/1.85  fof(f36,plain,(
% 11.50/1.85    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 11.50/1.85    introduced(choice_axiom,[])).
% 11.50/1.85  fof(f35,plain,(
% 11.50/1.85    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 11.50/1.85    inference(nnf_transformation,[],[f26])).
% 11.50/1.85  fof(f26,plain,(
% 11.50/1.85    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 11.50/1.85    inference(ennf_transformation,[],[f3])).
% 11.50/1.85  fof(f3,axiom,(
% 11.50/1.85    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 11.50/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 11.50/1.85  fof(f992,plain,(
% 11.50/1.85    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f87,f751,f54])).
% 11.50/1.85  fof(f54,plain,(
% 11.50/1.85    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 11.50/1.85    inference(cnf_transformation,[],[f34])).
% 11.50/1.85  fof(f34,plain,(
% 11.50/1.85    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 11.50/1.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f33])).
% 11.50/1.85  fof(f33,plain,(
% 11.50/1.85    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 11.50/1.85    introduced(choice_axiom,[])).
% 11.50/1.85  fof(f24,plain,(
% 11.50/1.85    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 11.50/1.85    inference(ennf_transformation,[],[f22])).
% 11.50/1.85  fof(f22,plain,(
% 11.50/1.85    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.50/1.85    inference(rectify,[],[f4])).
% 11.50/1.85  fof(f4,axiom,(
% 11.50/1.85    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 11.50/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 11.50/1.85  fof(f751,plain,(
% 11.50/1.85    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f747,f71])).
% 11.50/1.85  fof(f71,plain,(
% 11.50/1.85    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 11.50/1.85    inference(cnf_transformation,[],[f29])).
% 11.50/1.85  fof(f29,plain,(
% 11.50/1.85    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 11.50/1.85    inference(ennf_transformation,[],[f7])).
% 11.50/1.85  fof(f7,axiom,(
% 11.50/1.85    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 11.50/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 11.50/1.85  fof(f747,plain,(
% 11.50/1.85    ( ! [X11] : (r1_tarski(k1_xboole_0,X11)) )),
% 11.50/1.85    inference(superposition,[],[f89,f111])).
% 11.50/1.85  fof(f111,plain,(
% 11.50/1.85    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,k4_xboole_0(X0,X0))) = X1) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f103,f55])).
% 11.50/1.85  fof(f55,plain,(
% 11.50/1.85    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 11.50/1.85    inference(cnf_transformation,[],[f25])).
% 11.50/1.85  fof(f25,plain,(
% 11.50/1.85    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 11.50/1.85    inference(ennf_transformation,[],[f12])).
% 11.50/1.85  fof(f12,axiom,(
% 11.50/1.85    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 11.50/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 11.50/1.85  fof(f103,plain,(
% 11.50/1.85    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f50,f69])).
% 11.50/1.85  fof(f69,plain,(
% 11.50/1.85    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 11.50/1.85    inference(cnf_transformation,[],[f28])).
% 11.50/1.85  fof(f28,plain,(
% 11.50/1.85    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.50/1.85    inference(ennf_transformation,[],[f11])).
% 11.50/1.85  fof(f11,axiom,(
% 11.50/1.85    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 11.50/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 11.50/1.85  fof(f50,plain,(
% 11.50/1.85    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.50/1.85    inference(cnf_transformation,[],[f14])).
% 11.50/1.85  fof(f14,axiom,(
% 11.50/1.85    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.50/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 11.50/1.85  fof(f89,plain,(
% 11.50/1.85    ( ! [X0,X1] : (r1_tarski(k1_xboole_0,k2_xboole_0(X0,X1))) )),
% 11.50/1.85    inference(superposition,[],[f64,f47])).
% 11.50/1.85  fof(f47,plain,(
% 11.50/1.85    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 11.50/1.85    inference(cnf_transformation,[],[f10])).
% 11.50/1.85  fof(f10,axiom,(
% 11.50/1.85    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 11.50/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 11.50/1.85  fof(f64,plain,(
% 11.50/1.85    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 11.50/1.85    inference(cnf_transformation,[],[f9])).
% 11.50/1.85  fof(f9,axiom,(
% 11.50/1.85    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 11.50/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).
% 11.50/1.85  fof(f87,plain,(
% 11.50/1.85    ( ! [X3] : (r2_hidden(X3,k4_enumset1(X3,X3,X3,X3,X3,X3))) )),
% 11.50/1.85    inference(equality_resolution,[],[f86])).
% 11.50/1.85  fof(f86,plain,(
% 11.50/1.85    ( ! [X3,X1] : (r2_hidden(X3,X1) | k4_enumset1(X3,X3,X3,X3,X3,X3) != X1) )),
% 11.50/1.85    inference(equality_resolution,[],[f82])).
% 11.50/1.85  fof(f82,plain,(
% 11.50/1.85    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k4_enumset1(X0,X0,X0,X0,X0,X0) != X1) )),
% 11.50/1.85    inference(definition_unfolding,[],[f59,f77])).
% 11.50/1.85  fof(f59,plain,(
% 11.50/1.85    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 11.50/1.85    inference(cnf_transformation,[],[f41])).
% 11.50/1.85  fof(f169,plain,(
% 11.50/1.85    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,X2)))) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f128,f128,f72])).
% 11.50/1.85  fof(f72,plain,(
% 11.50/1.85    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 11.50/1.85    inference(cnf_transformation,[],[f44])).
% 11.50/1.85  fof(f44,plain,(
% 11.50/1.85    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 11.50/1.85    inference(nnf_transformation,[],[f30])).
% 11.50/1.85  fof(f30,plain,(
% 11.50/1.85    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 11.50/1.85    inference(ennf_transformation,[],[f2])).
% 11.50/1.85  fof(f2,axiom,(
% 11.50/1.85    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 11.50/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 11.50/1.85  fof(f128,plain,(
% 11.50/1.85    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(k1_xboole_0,X1))) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f87,f117,f54])).
% 11.50/1.85  fof(f117,plain,(
% 11.50/1.85    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f105,f71])).
% 11.50/1.85  fof(f105,plain,(
% 11.50/1.85    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(k1_xboole_0,X0),X1)) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f89,f69])).
% 11.50/1.85  fof(f941,plain,(
% 11.50/1.85    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X0) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k1_xboole_0,X2))) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f125,f169,f56])).
% 11.50/1.85  fof(f125,plain,(
% 11.50/1.85    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X1))) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f87,f109,f54])).
% 11.50/1.85  fof(f109,plain,(
% 11.50/1.85    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X0),X1)) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f103,f71])).
% 11.50/1.85  fof(f773,plain,(
% 11.50/1.85    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X1,X1)) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f125,f128,f56])).
% 11.50/1.85  fof(f4548,plain,(
% 11.50/1.85    ( ! [X16] : (k4_xboole_0(k5_xboole_0(k1_xboole_0,X16),k1_xboole_0) = k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(X16,k1_xboole_0)),k4_xboole_0(X16,k1_xboole_0))) )),
% 11.50/1.85    inference(superposition,[],[f68,f2599])).
% 11.50/1.85  fof(f2599,plain,(
% 11.50/1.85    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 11.50/1.85    inference(superposition,[],[f749,f1302])).
% 11.50/1.85  fof(f68,plain,(
% 11.50/1.85    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))) )),
% 11.50/1.85    inference(cnf_transformation,[],[f15])).
% 11.50/1.85  fof(f15,axiom,(
% 11.50/1.85    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))),
% 11.50/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_xboole_1)).
% 11.50/1.85  fof(f4576,plain,(
% 11.50/1.85    ( ! [X16] : (k4_xboole_0(X16,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X16,k1_xboole_0),k1_xboole_0)) )),
% 11.50/1.85    inference(forward_demodulation,[],[f4575,f4016])).
% 11.50/1.85  fof(f4016,plain,(
% 11.50/1.85    ( ! [X12] : (k4_xboole_0(X12,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X12,k1_xboole_0),k1_xboole_0)) )),
% 11.50/1.85    inference(forward_demodulation,[],[f4015,f1984])).
% 11.50/1.85  fof(f1984,plain,(
% 11.50/1.85    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 11.50/1.85    inference(forward_demodulation,[],[f1624,f1302])).
% 11.50/1.85  fof(f1624,plain,(
% 11.50/1.85    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) )),
% 11.50/1.85    inference(backward_demodulation,[],[f1061,f1302])).
% 11.50/1.85  fof(f4015,plain,(
% 11.50/1.85    ( ! [X12] : (k4_xboole_0(X12,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X12,k1_xboole_0),k1_xboole_0)) )),
% 11.50/1.85    inference(forward_demodulation,[],[f3987,f47])).
% 11.50/1.85  fof(f3987,plain,(
% 11.50/1.85    ( ! [X12] : (k4_xboole_0(X12,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X12,k1_xboole_0),k3_xboole_0(k3_xboole_0(X12,k1_xboole_0),k1_xboole_0))) )),
% 11.50/1.85    inference(superposition,[],[f67,f2599])).
% 11.50/1.85  fof(f67,plain,(
% 11.50/1.85    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 11.50/1.85    inference(cnf_transformation,[],[f6])).
% 11.50/1.85  fof(f6,axiom,(
% 11.50/1.85    ! [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2))),
% 11.50/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_xboole_1)).
% 11.50/1.85  fof(f4575,plain,(
% 11.50/1.85    ( ! [X16] : (k2_xboole_0(k4_xboole_0(X16,k1_xboole_0),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X16,k1_xboole_0),k1_xboole_0)) )),
% 11.50/1.85    inference(forward_demodulation,[],[f4532,f1302])).
% 11.50/1.85  fof(f4532,plain,(
% 11.50/1.85    ( ! [X16] : (k4_xboole_0(k5_xboole_0(X16,k1_xboole_0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X16,k1_xboole_0),k4_xboole_0(k1_xboole_0,k2_xboole_0(X16,k1_xboole_0)))) )),
% 11.50/1.85    inference(superposition,[],[f68,f2599])).
% 11.50/1.85  fof(f749,plain,(
% 11.50/1.85    ( ! [X15] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X15,k1_xboole_0)) = X15) )),
% 11.50/1.85    inference(superposition,[],[f99,f111])).
% 11.50/1.85  fof(f99,plain,(
% 11.50/1.85    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0))) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f89,f55])).
% 11.50/1.85  fof(f2709,plain,(
% 11.50/1.85    ( ! [X2,X3] : (k4_xboole_0(X2,k3_xboole_0(X2,X3)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,X3))) )),
% 11.50/1.85    inference(superposition,[],[f65,f1101])).
% 11.50/1.85  fof(f65,plain,(
% 11.50/1.85    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 11.50/1.85    inference(cnf_transformation,[],[f5])).
% 11.50/1.85  fof(f5,axiom,(
% 11.50/1.85    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 11.50/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).
% 11.50/1.85  fof(f90,plain,(
% 11.50/1.85    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X2,X1)) | ~r2_hidden(X0,X1)) )),
% 11.50/1.85    inference(resolution,[],[f54,f49])).
% 11.50/1.85  fof(f49,plain,(
% 11.50/1.85    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 11.50/1.85    inference(cnf_transformation,[],[f13])).
% 11.50/1.85  fof(f13,axiom,(
% 11.50/1.85    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 11.50/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 11.50/1.85  fof(f11018,plain,(
% 11.50/1.85    ( ! [X6,X7,X5] : (~r2_hidden(X7,k4_xboole_0(X5,X6)) | r2_hidden(X7,X5) | r2_hidden(X7,k3_xboole_0(X5,X6))) )),
% 11.50/1.85    inference(superposition,[],[f72,f10593])).
% 11.50/1.85  fof(f10593,plain,(
% 11.50/1.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.50/1.85    inference(forward_demodulation,[],[f10592,f4684])).
% 11.50/1.85  fof(f4684,plain,(
% 11.50/1.85    ( ! [X12] : (k2_xboole_0(X12,k1_xboole_0) = X12) )),
% 11.50/1.85    inference(backward_demodulation,[],[f4016,f4637])).
% 11.50/1.85  fof(f10592,plain,(
% 11.50/1.85    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.50/1.85    inference(forward_demodulation,[],[f10591,f1101])).
% 11.50/1.85  fof(f10591,plain,(
% 11.50/1.85    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0))) )),
% 11.50/1.85    inference(forward_demodulation,[],[f10590,f4845])).
% 11.50/1.85  fof(f4845,plain,(
% 11.50/1.85    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 11.50/1.85    inference(forward_demodulation,[],[f4691,f4639])).
% 11.50/1.85  fof(f4691,plain,(
% 11.50/1.85    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))) = X0) )),
% 11.50/1.85    inference(backward_demodulation,[],[f4068,f4637])).
% 11.50/1.85  fof(f4068,plain,(
% 11.50/1.85    ( ! [X0,X1] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k3_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1),k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)))) )),
% 11.50/1.85    inference(forward_demodulation,[],[f4055,f2709])).
% 11.50/1.85  fof(f4055,plain,(
% 11.50/1.85    ( ! [X0,X1] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k3_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1),k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k3_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)))) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f4036,f55])).
% 11.50/1.85  fof(f4036,plain,(
% 11.50/1.85    ( ! [X4,X3] : (r1_tarski(k3_xboole_0(k4_xboole_0(X3,k1_xboole_0),X4),k4_xboole_0(X3,k1_xboole_0))) )),
% 11.50/1.85    inference(superposition,[],[f64,f4016])).
% 11.50/1.85  fof(f10590,plain,(
% 11.50/1.85    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))))) )),
% 11.50/1.85    inference(forward_demodulation,[],[f10550,f7705])).
% 11.50/1.85  fof(f7705,plain,(
% 11.50/1.85    ( ! [X4,X5,X3] : (k4_xboole_0(k5_xboole_0(X3,k3_xboole_0(X3,X4)),X5) = k4_xboole_0(X3,k2_xboole_0(k3_xboole_0(X3,X4),X5))) )),
% 11.50/1.85    inference(forward_demodulation,[],[f7653,f4684])).
% 11.50/1.85  fof(f7653,plain,(
% 11.50/1.85    ( ! [X4,X5,X3] : (k4_xboole_0(k5_xboole_0(X3,k3_xboole_0(X3,X4)),X5) = k2_xboole_0(k4_xboole_0(X3,k2_xboole_0(k3_xboole_0(X3,X4),X5)),k1_xboole_0)) )),
% 11.50/1.85    inference(superposition,[],[f68,f5902])).
% 11.50/1.85  fof(f5902,plain,(
% 11.50/1.85    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f64,f5416])).
% 11.50/1.85  fof(f5416,plain,(
% 11.50/1.85    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 11.50/1.85    inference(resolution,[],[f4841,f4650])).
% 11.50/1.85  fof(f4650,plain,(
% 11.50/1.85    ( ! [X8] : (~r1_tarski(X8,k1_xboole_0) | k1_xboole_0 = X8) )),
% 11.50/1.85    inference(backward_demodulation,[],[f2675,f4637])).
% 11.50/1.85  fof(f2675,plain,(
% 11.50/1.85    ( ! [X8] : (~r1_tarski(X8,k1_xboole_0) | k1_xboole_0 = k4_xboole_0(X8,k1_xboole_0)) )),
% 11.50/1.85    inference(resolution,[],[f2668,f1905])).
% 11.50/1.85  fof(f1905,plain,(
% 11.50/1.85    ( ! [X8] : (r2_hidden(sK3(X8,k1_xboole_0),X8) | k1_xboole_0 = X8) )),
% 11.50/1.85    inference(forward_demodulation,[],[f1867,f1792])).
% 11.50/1.85  fof(f1792,plain,(
% 11.50/1.85    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_xboole_0,X2),X3)) )),
% 11.50/1.85    inference(backward_demodulation,[],[f831,f1601])).
% 11.50/1.85  fof(f1601,plain,(
% 11.50/1.85    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X1,X2),X1)) )),
% 11.50/1.85    inference(backward_demodulation,[],[f788,f1302])).
% 11.50/1.85  fof(f788,plain,(
% 11.50/1.85    ( ! [X2,X0,X1] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k3_xboole_0(X1,X2),X1)) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f128,f162,f56])).
% 11.50/1.85  fof(f162,plain,(
% 11.50/1.85    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(k3_xboole_0(X1,X2),X1))) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f87,f145,f54])).
% 11.50/1.85  fof(f145,plain,(
% 11.50/1.85    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X0),X2)) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f104,f71])).
% 11.50/1.85  fof(f104,plain,(
% 11.50/1.85    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(k3_xboole_0(X0,X1),X0),X2)) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f64,f69])).
% 11.50/1.85  fof(f831,plain,(
% 11.50/1.85    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X0) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X2),X3)) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f162,f639,f56])).
% 11.50/1.85  fof(f639,plain,(
% 11.50/1.85    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(k3_xboole_0(k1_xboole_0,X1),X2))) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f87,f630,f54])).
% 11.50/1.85  fof(f630,plain,(
% 11.50/1.85    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1),X2)) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f623,f71])).
% 11.50/1.85  fof(f623,plain,(
% 11.50/1.85    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1),X2)) )),
% 11.50/1.85    inference(unit_resulting_resolution,[],[f621,f69])).
% 11.50/1.85  fof(f621,plain,(
% 11.50/1.85    ( ! [X10,X8,X9] : (r1_tarski(k3_xboole_0(k1_xboole_0,X10),k2_xboole_0(X8,X9))) )),
% 11.50/1.85    inference(superposition,[],[f64,f99])).
% 11.50/1.85  fof(f1867,plain,(
% 11.50/1.85    ( ! [X10,X8,X9] : (r2_hidden(sK3(X8,k1_xboole_0),X8) | k4_xboole_0(k3_xboole_0(k1_xboole_0,X9),X10) = X8) )),
% 11.50/1.85    inference(backward_demodulation,[],[f958,f1792])).
% 11.50/1.86  fof(f958,plain,(
% 11.50/1.86    ( ! [X10,X8,X9] : (r2_hidden(sK3(X8,k4_xboole_0(k3_xboole_0(k1_xboole_0,X9),X10)),X8) | k4_xboole_0(k3_xboole_0(k1_xboole_0,X9),X10) = X8) )),
% 11.50/1.86    inference(resolution,[],[f56,f639])).
% 11.50/1.86  fof(f2668,plain,(
% 11.50/1.86    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k1_xboole_0)) | ~r1_tarski(X1,k1_xboole_0)) )),
% 11.50/1.86    inference(condensation,[],[f2664])).
% 11.50/1.86  fof(f2664,plain,(
% 11.50/1.86    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_xboole_0) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,k4_xboole_0(X0,k1_xboole_0))) )),
% 11.50/1.86    inference(resolution,[],[f2645,f54])).
% 11.50/1.86  fof(f2645,plain,(
% 11.50/1.86    ( ! [X2,X3] : (r1_xboole_0(k4_xboole_0(X2,k1_xboole_0),X3) | ~r1_tarski(X2,k1_xboole_0)) )),
% 11.50/1.86    inference(resolution,[],[f2610,f2511])).
% 11.50/1.86  fof(f2511,plain,(
% 11.50/1.86    ( ! [X2,X3] : (~r1_tarski(X3,k1_xboole_0) | r1_xboole_0(X3,X2)) )),
% 11.50/1.86    inference(superposition,[],[f71,f1302])).
% 11.50/1.86  fof(f2610,plain,(
% 11.50/1.86    ( ! [X1] : (r1_tarski(k4_xboole_0(X1,k1_xboole_0),k1_xboole_0) | ~r1_tarski(X1,k1_xboole_0)) )),
% 11.50/1.86    inference(superposition,[],[f69,f2599])).
% 11.50/1.86  fof(f4841,plain,(
% 11.50/1.86    ( ! [X8,X7] : (r1_tarski(k4_xboole_0(X8,X7),k1_xboole_0) | ~r1_tarski(X8,X7)) )),
% 11.50/1.86    inference(forward_demodulation,[],[f4687,f4637])).
% 11.50/1.86  fof(f4687,plain,(
% 11.50/1.86    ( ! [X8,X7] : (~r1_tarski(X8,X7) | r1_tarski(k4_xboole_0(X8,k4_xboole_0(X7,k1_xboole_0)),k1_xboole_0)) )),
% 11.50/1.86    inference(backward_demodulation,[],[f4038,f4637])).
% 11.50/1.86  fof(f4038,plain,(
% 11.50/1.86    ( ! [X8,X7] : (~r1_tarski(X8,k4_xboole_0(X7,k1_xboole_0)) | r1_tarski(k4_xboole_0(X8,k4_xboole_0(X7,k1_xboole_0)),k1_xboole_0)) )),
% 11.50/1.86    inference(superposition,[],[f69,f4016])).
% 11.50/1.86  fof(f10550,plain,(
% 11.50/1.86    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k4_xboole_0(X0,X1)))) )),
% 11.50/1.86    inference(unit_resulting_resolution,[],[f10162,f55])).
% 11.50/1.86  fof(f10162,plain,(
% 11.50/1.86    ( ! [X24,X25] : (r1_tarski(k4_xboole_0(X24,X25),k5_xboole_0(X24,k3_xboole_0(X24,X25)))) )),
% 11.50/1.86    inference(superposition,[],[f10104,f4780])).
% 11.50/1.86  fof(f10104,plain,(
% 11.50/1.86    ( ! [X35,X36] : (r1_tarski(k4_xboole_0(X36,X35),k5_xboole_0(X36,X35))) )),
% 11.50/1.86    inference(forward_demodulation,[],[f10066,f4637])).
% 11.50/1.86  fof(f10066,plain,(
% 11.50/1.86    ( ! [X35,X36] : (r1_tarski(k4_xboole_0(X36,X35),k4_xboole_0(k5_xboole_0(X36,X35),k1_xboole_0))) )),
% 11.50/1.86    inference(superposition,[],[f4561,f4684])).
% 11.50/1.86  fof(f4561,plain,(
% 11.50/1.86    ( ! [X4,X2,X3] : (r1_tarski(k4_xboole_0(X2,k2_xboole_0(X3,X4)),k4_xboole_0(k5_xboole_0(X2,X3),X4))) )),
% 11.50/1.86    inference(superposition,[],[f50,f68])).
% 11.50/1.86  fof(f5665,plain,(
% 11.50/1.86    r2_hidden(sK5(k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1),sK0),k4_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 11.50/1.86    inference(unit_resulting_resolution,[],[f79,f78,f85])).
% 11.50/1.86  fof(f85,plain,(
% 11.50/1.86    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | k1_xboole_0 = X0 | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0) )),
% 11.50/1.86    inference(definition_unfolding,[],[f62,f77])).
% 11.50/1.86  fof(f62,plain,(
% 11.50/1.86    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 11.50/1.86    inference(cnf_transformation,[],[f43])).
% 11.50/1.86  % SZS output end Proof for theBenchmark
% 11.50/1.86  % (24098)------------------------------
% 11.50/1.86  % (24098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.50/1.86  % (24098)Termination reason: Refutation
% 11.50/1.86  
% 11.50/1.86  % (24098)Memory used [KB]: 14456
% 11.50/1.86  % (24098)Time elapsed: 0.900 s
% 11.50/1.86  % (24098)------------------------------
% 11.50/1.86  % (24098)------------------------------
% 11.50/1.86  % (24031)Success in time 1.484 s
%------------------------------------------------------------------------------
