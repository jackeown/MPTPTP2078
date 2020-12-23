%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:02 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 294 expanded)
%              Number of leaves         :   17 (  82 expanded)
%              Depth                    :   21
%              Number of atoms          :  172 ( 745 expanded)
%              Number of equality atoms :   42 ( 113 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f785,plain,(
    $false ),
    inference(subsumption_resolution,[],[f778,f36])).

fof(f36,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f778,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f60,f772])).

fof(f772,plain,(
    sK1 = k2_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f771,f349])).

fof(f349,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f336,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f336,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,X4) ),
    inference(backward_demodulation,[],[f83,f334])).

fof(f334,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f327,f239])).

fof(f239,plain,(
    ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) = X3 ),
    inference(forward_demodulation,[],[f231,f218])).

fof(f218,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X0) = X0 ),
    inference(resolution,[],[f211,f48])).

fof(f211,plain,(
    ! [X2] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X2) ),
    inference(resolution,[],[f207,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f207,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f56,f35])).

fof(f35,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f44,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f231,plain,(
    ! [X3] : k4_xboole_0(X3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X3) ),
    inference(superposition,[],[f218,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f327,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) ),
    inference(resolution,[],[f59,f210])).

fof(f210,plain,(
    ! [X1] : r1_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f207,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f52,f40])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f83,plain,(
    ! [X4] : r1_tarski(k4_xboole_0(X4,X4),X4) ),
    inference(superposition,[],[f77,f74])).

fof(f74,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f73,f48])).

fof(f73,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f51,f50])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f60,f41])).

fof(f771,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f768,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f768,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f41,f748])).

fof(f748,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f727,f546])).

fof(f546,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f495,f64])).

fof(f64,plain,(
    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f48,f34])).

fof(f34,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f495,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f492,f39])).

fof(f492,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f454,f41])).

fof(f454,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f54,f334])).

fof(f54,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f727,plain,(
    ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK2)) ),
    inference(superposition,[],[f713,f39])).

fof(f713,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[],[f54,f697])).

fof(f697,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f675,f37])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f675,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f55,f332])).

fof(f332,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f59,f35])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f42,f40])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f38,f39])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:42:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (7052)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.49  % (7044)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.50  % (7027)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (7036)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (7036)Refutation not found, incomplete strategy% (7036)------------------------------
% 0.21/0.50  % (7036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7036)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (7036)Memory used [KB]: 10618
% 0.21/0.50  % (7036)Time elapsed: 0.088 s
% 0.21/0.50  % (7036)------------------------------
% 0.21/0.50  % (7036)------------------------------
% 0.21/0.51  % (7045)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (7030)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (7029)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (7047)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (7034)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (7037)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (7028)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (7042)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (7039)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (7038)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.53  % (7040)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.33/0.53  % (7055)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.33/0.53  % (7051)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.33/0.53  % (7053)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.33/0.53  % (7031)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.33/0.53  % (7026)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.33/0.53  % (7043)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.33/0.53  % (7050)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.33/0.53  % (7035)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.33/0.53  % (7035)Refutation not found, incomplete strategy% (7035)------------------------------
% 1.33/0.53  % (7035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (7035)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (7035)Memory used [KB]: 10618
% 1.33/0.53  % (7035)Time elapsed: 0.132 s
% 1.33/0.53  % (7035)------------------------------
% 1.33/0.53  % (7035)------------------------------
% 1.33/0.53  % (7049)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.33/0.53  % (7026)Refutation not found, incomplete strategy% (7026)------------------------------
% 1.33/0.53  % (7026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (7026)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (7026)Memory used [KB]: 1663
% 1.33/0.53  % (7026)Time elapsed: 0.125 s
% 1.33/0.53  % (7026)------------------------------
% 1.33/0.53  % (7026)------------------------------
% 1.33/0.54  % (7054)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.33/0.54  % (7041)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.33/0.54  % (7043)Refutation not found, incomplete strategy% (7043)------------------------------
% 1.33/0.54  % (7043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (7043)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (7043)Memory used [KB]: 10618
% 1.33/0.54  % (7043)Time elapsed: 0.129 s
% 1.33/0.54  % (7043)------------------------------
% 1.33/0.54  % (7043)------------------------------
% 1.33/0.54  % (7033)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.33/0.54  % (7032)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.33/0.54  % (7046)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.33/0.54  % (7029)Refutation found. Thanks to Tanya!
% 1.33/0.54  % SZS status Theorem for theBenchmark
% 1.47/0.54  % (7037)Refutation not found, incomplete strategy% (7037)------------------------------
% 1.47/0.54  % (7037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.54  % (7037)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.54  
% 1.47/0.54  % (7037)Memory used [KB]: 10618
% 1.47/0.54  % (7037)Time elapsed: 0.125 s
% 1.47/0.54  % (7037)------------------------------
% 1.47/0.54  % (7037)------------------------------
% 1.47/0.55  % (7048)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.47/0.56  % SZS output start Proof for theBenchmark
% 1.47/0.56  fof(f785,plain,(
% 1.47/0.56    $false),
% 1.47/0.56    inference(subsumption_resolution,[],[f778,f36])).
% 1.47/0.56  fof(f36,plain,(
% 1.47/0.56    ~r1_tarski(sK0,sK1)),
% 1.47/0.56    inference(cnf_transformation,[],[f24])).
% 1.47/0.56  fof(f24,plain,(
% 1.47/0.56    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f23])).
% 1.47/0.56  fof(f23,plain,(
% 1.47/0.56    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f18,plain,(
% 1.47/0.56    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.47/0.56    inference(flattening,[],[f17])).
% 1.47/0.56  fof(f17,plain,(
% 1.47/0.56    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.47/0.56    inference(ennf_transformation,[],[f14])).
% 1.47/0.56  fof(f14,negated_conjecture,(
% 1.47/0.56    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 1.47/0.56    inference(negated_conjecture,[],[f13])).
% 1.47/0.56  fof(f13,conjecture,(
% 1.47/0.56    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 1.47/0.56  fof(f778,plain,(
% 1.47/0.56    r1_tarski(sK0,sK1)),
% 1.47/0.56    inference(superposition,[],[f60,f772])).
% 1.47/0.56  fof(f772,plain,(
% 1.47/0.56    sK1 = k2_xboole_0(sK1,sK0)),
% 1.47/0.56    inference(forward_demodulation,[],[f771,f349])).
% 1.47/0.56  fof(f349,plain,(
% 1.47/0.56    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.47/0.56    inference(resolution,[],[f336,f48])).
% 1.47/0.56  fof(f48,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.47/0.56    inference(cnf_transformation,[],[f21])).
% 1.47/0.56  fof(f21,plain,(
% 1.47/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.47/0.56    inference(ennf_transformation,[],[f6])).
% 1.47/0.56  fof(f6,axiom,(
% 1.47/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.47/0.56  fof(f336,plain,(
% 1.47/0.56    ( ! [X4] : (r1_tarski(k1_xboole_0,X4)) )),
% 1.47/0.56    inference(backward_demodulation,[],[f83,f334])).
% 1.47/0.56  fof(f334,plain,(
% 1.47/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.47/0.56    inference(forward_demodulation,[],[f327,f239])).
% 1.47/0.56  fof(f239,plain,(
% 1.47/0.56    ( ! [X3] : (k4_xboole_0(X3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) = X3) )),
% 1.47/0.56    inference(forward_demodulation,[],[f231,f218])).
% 1.47/0.56  fof(f218,plain,(
% 1.47/0.56    ( ! [X0] : (k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X0) = X0) )),
% 1.47/0.56    inference(resolution,[],[f211,f48])).
% 1.47/0.56  fof(f211,plain,(
% 1.47/0.56    ( ! [X2] : (r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X2)) )),
% 1.47/0.56    inference(resolution,[],[f207,f50])).
% 1.47/0.56  fof(f50,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f32])).
% 1.47/0.56  fof(f32,plain,(
% 1.47/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f31])).
% 1.47/0.56  fof(f31,plain,(
% 1.47/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f30,plain,(
% 1.47/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.56    inference(rectify,[],[f29])).
% 1.47/0.56  fof(f29,plain,(
% 1.47/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.56    inference(nnf_transformation,[],[f22])).
% 1.47/0.56  fof(f22,plain,(
% 1.47/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.47/0.56    inference(ennf_transformation,[],[f2])).
% 1.47/0.56  fof(f2,axiom,(
% 1.47/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.47/0.56  fof(f207,plain,(
% 1.47/0.56    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) )),
% 1.47/0.56    inference(resolution,[],[f56,f35])).
% 1.47/0.56  fof(f35,plain,(
% 1.47/0.56    r1_xboole_0(sK0,sK2)),
% 1.47/0.56    inference(cnf_transformation,[],[f24])).
% 1.47/0.56  fof(f56,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.47/0.56    inference(definition_unfolding,[],[f44,f40])).
% 1.47/0.56  fof(f40,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f11])).
% 1.47/0.56  fof(f11,axiom,(
% 1.47/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.47/0.56  fof(f44,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f26])).
% 1.47/0.56  fof(f26,plain,(
% 1.47/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f25])).
% 1.47/0.56  fof(f25,plain,(
% 1.47/0.56    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f19,plain,(
% 1.47/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.47/0.56    inference(ennf_transformation,[],[f15])).
% 1.47/0.56  fof(f15,plain,(
% 1.47/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.47/0.56    inference(rectify,[],[f5])).
% 1.47/0.56  fof(f5,axiom,(
% 1.47/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.47/0.56  fof(f231,plain,(
% 1.47/0.56    ( ! [X3] : (k4_xboole_0(X3,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X3)) )),
% 1.47/0.56    inference(superposition,[],[f218,f41])).
% 1.47/0.56  fof(f41,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f7])).
% 1.47/0.56  fof(f7,axiom,(
% 1.47/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.47/0.56  fof(f327,plain,(
% 1.47/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))))) )),
% 1.47/0.56    inference(resolution,[],[f59,f210])).
% 1.47/0.56  fof(f210,plain,(
% 1.47/0.56    ( ! [X1] : (r1_xboole_0(X1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) )),
% 1.47/0.56    inference(resolution,[],[f207,f46])).
% 1.47/0.56  fof(f46,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f28])).
% 1.47/0.56  fof(f28,plain,(
% 1.47/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f27])).
% 1.47/0.56  fof(f27,plain,(
% 1.47/0.56    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f20,plain,(
% 1.47/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.47/0.56    inference(ennf_transformation,[],[f16])).
% 1.47/0.56  fof(f16,plain,(
% 1.47/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.47/0.56    inference(rectify,[],[f4])).
% 1.47/0.56  fof(f4,axiom,(
% 1.47/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.47/0.56  fof(f59,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.47/0.56    inference(definition_unfolding,[],[f52,f40])).
% 1.47/0.56  fof(f52,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f33])).
% 1.47/0.56  fof(f33,plain,(
% 1.47/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.47/0.56    inference(nnf_transformation,[],[f3])).
% 1.47/0.56  fof(f3,axiom,(
% 1.47/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.47/0.56  fof(f83,plain,(
% 1.47/0.56    ( ! [X4] : (r1_tarski(k4_xboole_0(X4,X4),X4)) )),
% 1.47/0.56    inference(superposition,[],[f77,f74])).
% 1.47/0.56  fof(f74,plain,(
% 1.47/0.56    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.47/0.56    inference(resolution,[],[f73,f48])).
% 1.47/0.56  fof(f73,plain,(
% 1.47/0.56    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.47/0.56    inference(duplicate_literal_removal,[],[f72])).
% 1.47/0.56  fof(f72,plain,(
% 1.47/0.56    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.47/0.56    inference(resolution,[],[f51,f50])).
% 1.47/0.56  fof(f51,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f32])).
% 1.47/0.56  fof(f77,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1))) )),
% 1.47/0.56    inference(superposition,[],[f60,f41])).
% 1.47/0.56  fof(f771,plain,(
% 1.47/0.56    k2_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,sK1)),
% 1.47/0.56    inference(forward_demodulation,[],[f768,f39])).
% 1.47/0.56  fof(f39,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f1])).
% 1.47/0.56  fof(f1,axiom,(
% 1.47/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.47/0.56  fof(f768,plain,(
% 1.47/0.56    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0)),
% 1.47/0.56    inference(superposition,[],[f41,f748])).
% 1.47/0.56  fof(f748,plain,(
% 1.47/0.56    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.47/0.56    inference(superposition,[],[f727,f546])).
% 1.47/0.56  fof(f546,plain,(
% 1.47/0.56    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.47/0.56    inference(superposition,[],[f495,f64])).
% 1.47/0.56  fof(f64,plain,(
% 1.47/0.56    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.47/0.56    inference(resolution,[],[f48,f34])).
% 1.47/0.56  fof(f34,plain,(
% 1.47/0.56    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 1.47/0.56    inference(cnf_transformation,[],[f24])).
% 1.47/0.56  fof(f495,plain,(
% 1.47/0.56    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X1))) )),
% 1.47/0.56    inference(superposition,[],[f492,f39])).
% 1.47/0.56  fof(f492,plain,(
% 1.47/0.56    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 1.47/0.56    inference(forward_demodulation,[],[f454,f41])).
% 1.47/0.56  fof(f454,plain,(
% 1.47/0.56    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 1.47/0.56    inference(superposition,[],[f54,f334])).
% 1.47/0.56  fof(f54,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f9])).
% 1.47/0.56  fof(f9,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.47/0.56  fof(f727,plain,(
% 1.47/0.56    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK2))) )),
% 1.47/0.56    inference(superposition,[],[f713,f39])).
% 1.47/0.56  fof(f713,plain,(
% 1.47/0.56    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)) )),
% 1.47/0.56    inference(superposition,[],[f54,f697])).
% 1.47/0.56  fof(f697,plain,(
% 1.47/0.56    sK0 = k4_xboole_0(sK0,sK2)),
% 1.47/0.56    inference(forward_demodulation,[],[f675,f37])).
% 1.47/0.56  fof(f37,plain,(
% 1.47/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.47/0.56    inference(cnf_transformation,[],[f8])).
% 1.47/0.56  fof(f8,axiom,(
% 1.47/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.47/0.56  fof(f675,plain,(
% 1.47/0.56    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.47/0.56    inference(superposition,[],[f55,f332])).
% 1.47/0.56  fof(f332,plain,(
% 1.47/0.56    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.47/0.56    inference(resolution,[],[f59,f35])).
% 1.47/0.56  fof(f55,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.47/0.56    inference(definition_unfolding,[],[f42,f40])).
% 1.47/0.56  fof(f42,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f10])).
% 1.47/0.56  fof(f10,axiom,(
% 1.47/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.47/0.56  fof(f60,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 1.47/0.56    inference(superposition,[],[f38,f39])).
% 1.47/0.56  fof(f38,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f12])).
% 1.47/0.56  fof(f12,axiom,(
% 1.47/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.47/0.56  % SZS output end Proof for theBenchmark
% 1.47/0.56  % (7029)------------------------------
% 1.47/0.56  % (7029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (7029)Termination reason: Refutation
% 1.47/0.56  
% 1.47/0.56  % (7029)Memory used [KB]: 11129
% 1.47/0.56  % (7029)Time elapsed: 0.122 s
% 1.47/0.56  % (7029)------------------------------
% 1.47/0.56  % (7029)------------------------------
% 1.47/0.56  % (7025)Success in time 0.198 s
%------------------------------------------------------------------------------
