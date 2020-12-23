%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:04 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 351 expanded)
%              Number of leaves         :   17 ( 106 expanded)
%              Depth                    :   31
%              Number of atoms          :  182 ( 598 expanded)
%              Number of equality atoms :   53 ( 217 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1971,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1947,f34])).

fof(f34,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f1947,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f59,f1934])).

fof(f1934,plain,(
    sK1 = k2_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f1933,f87])).

fof(f87,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f82,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f82,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f77,f35])).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f77,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f41,f35])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1933,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f1921,f37])).

fof(f1921,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f39,f1895])).

fof(f1895,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f1894,f87])).

fof(f1894,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f1878,f37])).

fof(f1878,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f1877,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1877,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1876,f959])).

fof(f959,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(X9,k2_xboole_0(X10,X9)) ),
    inference(backward_demodulation,[],[f438,f946])).

fof(f946,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(X4,X4) ),
    inference(forward_demodulation,[],[f940,f35])).

fof(f940,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)) ),
    inference(resolution,[],[f56,f281])).

fof(f281,plain,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[],[f279,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f279,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f277,f181])).

fof(f181,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f178,f170])).

fof(f170,plain,(
    ! [X15,X16] :
      ( ~ r1_xboole_0(X15,X16)
      | r1_xboole_0(k1_xboole_0,X16) ) ),
    inference(resolution,[],[f51,f92])).

fof(f92,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,X4) ),
    inference(superposition,[],[f59,f82])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f178,plain,(
    r1_xboole_0(sK2,k1_xboole_0) ),
    inference(resolution,[],[f175,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f175,plain,(
    r1_xboole_0(k1_xboole_0,sK2) ),
    inference(resolution,[],[f170,f33])).

fof(f33,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f277,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ) ),
    inference(superposition,[],[f267,f35])).

fof(f267,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k4_xboole_0(X0,X0))
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f53,f35])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f48,f38])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f438,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k2_xboole_0(X10,X9)) = k4_xboole_0(k2_xboole_0(X10,X9),k2_xboole_0(X10,X9)) ),
    inference(superposition,[],[f41,f401])).

fof(f401,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f329,f37])).

fof(f329,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(X8,k2_xboole_0(X8,X9)) ),
    inference(forward_demodulation,[],[f323,f39])).

fof(f323,plain,(
    ! [X8,X9] : k2_xboole_0(X8,k2_xboole_0(X8,X9)) = k2_xboole_0(X8,k4_xboole_0(X9,X8)) ),
    inference(superposition,[],[f39,f74])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f41,f37])).

fof(f1876,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))) ),
    inference(forward_demodulation,[],[f1874,f50])).

fof(f1874,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)) ),
    inference(resolution,[],[f1873,f56])).

fof(f1873,plain,(
    r1_xboole_0(k4_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f1849,f47])).

fof(f1849,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f1807,f164])).

fof(f164,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k2_xboole_0(sK1,sK2),X0)
      | r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f51,f32])).

fof(f32,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f1807,plain,(
    ! [X0] : r1_xboole_0(k2_xboole_0(X0,sK2),k4_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f1749,f37])).

fof(f1749,plain,(
    ! [X17] : r1_xboole_0(k2_xboole_0(sK2,X17),k4_xboole_0(sK0,X17)) ),
    inference(superposition,[],[f1025,f1699])).

fof(f1699,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[],[f50,f1657])).

fof(f1657,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f1625,f35])).

fof(f1625,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f52,f944])).

fof(f944,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f56,f33])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f38])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f1025,plain,(
    ! [X2,X3] : r1_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(resolution,[],[f975,f47])).

fof(f975,plain,(
    ! [X8,X7] : r1_xboole_0(k4_xboole_0(X7,X8),X8) ),
    inference(trivial_inequality_removal,[],[f974])).

fof(f974,plain,(
    ! [X8,X7] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k4_xboole_0(X7,X8),X8) ) ),
    inference(backward_demodulation,[],[f686,f947])).

fof(f947,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3) ),
    inference(backward_demodulation,[],[f102,f946])).

fof(f102,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X3,X3) ),
    inference(superposition,[],[f41,f87])).

fof(f686,plain,(
    ! [X8,X7] :
      ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k4_xboole_0(X7,X8))
      | r1_xboole_0(k4_xboole_0(X7,X8),X8) ) ),
    inference(forward_demodulation,[],[f684,f102])).

fof(f684,plain,(
    ! [X8,X7] :
      ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,X8))
      | r1_xboole_0(k4_xboole_0(X7,X8),X8) ) ),
    inference(superposition,[],[f55,f325])).

fof(f325,plain,(
    ! [X6,X7] : k4_xboole_0(X7,X6) = k4_xboole_0(k4_xboole_0(X7,X6),X6) ),
    inference(forward_demodulation,[],[f316,f74])).

fof(f316,plain,(
    ! [X6,X7] : k4_xboole_0(k4_xboole_0(X7,X6),X6) = k4_xboole_0(k2_xboole_0(X6,X7),X6) ),
    inference(superposition,[],[f74,f39])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f38])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f36,f37])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:54:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.44  % (26682)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.45  % (26690)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.45  % (26692)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.45  % (26681)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (26684)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (26679)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (26691)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (26686)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.46  % (26688)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (26680)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (26677)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (26683)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (26678)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (26687)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (26689)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (26685)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (26693)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (26694)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.38/0.53  % (26686)Refutation found. Thanks to Tanya!
% 1.38/0.53  % SZS status Theorem for theBenchmark
% 1.38/0.53  % SZS output start Proof for theBenchmark
% 1.38/0.53  fof(f1971,plain,(
% 1.38/0.53    $false),
% 1.38/0.53    inference(subsumption_resolution,[],[f1947,f34])).
% 1.38/0.53  fof(f34,plain,(
% 1.38/0.53    ~r1_tarski(sK0,sK1)),
% 1.38/0.53    inference(cnf_transformation,[],[f26])).
% 1.38/0.53  fof(f26,plain,(
% 1.38/0.53    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 1.38/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f25])).
% 1.38/0.53  fof(f25,plain,(
% 1.38/0.53    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 1.38/0.53    introduced(choice_axiom,[])).
% 1.38/0.53  fof(f19,plain,(
% 1.38/0.53    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.38/0.53    inference(flattening,[],[f18])).
% 1.38/0.53  fof(f18,plain,(
% 1.38/0.53    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.38/0.53    inference(ennf_transformation,[],[f15])).
% 1.38/0.53  fof(f15,negated_conjecture,(
% 1.38/0.53    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 1.38/0.53    inference(negated_conjecture,[],[f14])).
% 1.38/0.53  fof(f14,conjecture,(
% 1.38/0.53    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 1.38/0.53  fof(f1947,plain,(
% 1.38/0.53    r1_tarski(sK0,sK1)),
% 1.38/0.53    inference(superposition,[],[f59,f1934])).
% 1.38/0.53  fof(f1934,plain,(
% 1.38/0.53    sK1 = k2_xboole_0(sK1,sK0)),
% 1.38/0.53    inference(forward_demodulation,[],[f1933,f87])).
% 1.38/0.53  fof(f87,plain,(
% 1.38/0.53    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.38/0.53    inference(superposition,[],[f82,f37])).
% 1.38/0.53  fof(f37,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f1])).
% 1.38/0.53  fof(f1,axiom,(
% 1.38/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.38/0.53  fof(f82,plain,(
% 1.38/0.53    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.38/0.53    inference(forward_demodulation,[],[f77,f35])).
% 1.38/0.53  fof(f35,plain,(
% 1.38/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.38/0.53    inference(cnf_transformation,[],[f7])).
% 1.38/0.53  fof(f7,axiom,(
% 1.38/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.38/0.53  fof(f77,plain,(
% 1.38/0.53    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 1.38/0.53    inference(superposition,[],[f41,f35])).
% 1.38/0.53  fof(f41,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f8])).
% 1.38/0.53  fof(f8,axiom,(
% 1.38/0.53    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.38/0.53  fof(f1933,plain,(
% 1.38/0.53    k2_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,sK1)),
% 1.38/0.53    inference(forward_demodulation,[],[f1921,f37])).
% 1.38/0.53  fof(f1921,plain,(
% 1.38/0.53    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0)),
% 1.38/0.53    inference(superposition,[],[f39,f1895])).
% 1.38/0.53  fof(f1895,plain,(
% 1.38/0.53    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.38/0.53    inference(forward_demodulation,[],[f1894,f87])).
% 1.38/0.53  fof(f1894,plain,(
% 1.38/0.53    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK1))),
% 1.38/0.53    inference(forward_demodulation,[],[f1878,f37])).
% 1.38/0.53  fof(f1878,plain,(
% 1.38/0.53    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0))),
% 1.38/0.53    inference(superposition,[],[f1877,f50])).
% 1.38/0.53  fof(f50,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f9])).
% 1.38/0.53  fof(f9,axiom,(
% 1.38/0.53    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.38/0.53  fof(f1877,plain,(
% 1.38/0.53    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 1.38/0.53    inference(forward_demodulation,[],[f1876,f959])).
% 1.38/0.53  fof(f959,plain,(
% 1.38/0.53    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(X9,k2_xboole_0(X10,X9))) )),
% 1.38/0.53    inference(backward_demodulation,[],[f438,f946])).
% 1.38/0.53  fof(f946,plain,(
% 1.38/0.53    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(X4,X4)) )),
% 1.38/0.53    inference(forward_demodulation,[],[f940,f35])).
% 1.38/0.53  fof(f940,plain,(
% 1.38/0.53    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0))) )),
% 1.38/0.53    inference(resolution,[],[f56,f281])).
% 1.38/0.53  fof(f281,plain,(
% 1.38/0.53    ( ! [X1] : (r1_xboole_0(X1,k1_xboole_0)) )),
% 1.38/0.53    inference(resolution,[],[f279,f45])).
% 1.38/0.53  fof(f45,plain,(
% 1.38/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f30])).
% 1.38/0.53  fof(f30,plain,(
% 1.38/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.38/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f29])).
% 1.38/0.53  fof(f29,plain,(
% 1.38/0.53    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.38/0.53    introduced(choice_axiom,[])).
% 1.38/0.53  fof(f21,plain,(
% 1.38/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.38/0.53    inference(ennf_transformation,[],[f17])).
% 1.38/0.53  fof(f17,plain,(
% 1.38/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.38/0.53    inference(rectify,[],[f4])).
% 1.38/0.53  fof(f4,axiom,(
% 1.38/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.38/0.53  fof(f279,plain,(
% 1.38/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.38/0.53    inference(subsumption_resolution,[],[f277,f181])).
% 1.38/0.53  fof(f181,plain,(
% 1.38/0.53    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.38/0.53    inference(resolution,[],[f178,f170])).
% 1.38/0.53  fof(f170,plain,(
% 1.38/0.53    ( ! [X15,X16] : (~r1_xboole_0(X15,X16) | r1_xboole_0(k1_xboole_0,X16)) )),
% 1.38/0.53    inference(resolution,[],[f51,f92])).
% 1.38/0.53  fof(f92,plain,(
% 1.38/0.53    ( ! [X4] : (r1_tarski(k1_xboole_0,X4)) )),
% 1.38/0.53    inference(superposition,[],[f59,f82])).
% 1.38/0.53  fof(f51,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f24])).
% 1.38/0.53  fof(f24,plain,(
% 1.38/0.53    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.38/0.53    inference(flattening,[],[f23])).
% 1.38/0.53  fof(f23,plain,(
% 1.38/0.53    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.38/0.53    inference(ennf_transformation,[],[f12])).
% 1.38/0.53  fof(f12,axiom,(
% 1.38/0.53    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.38/0.53  fof(f178,plain,(
% 1.38/0.53    r1_xboole_0(sK2,k1_xboole_0)),
% 1.38/0.53    inference(resolution,[],[f175,f47])).
% 1.38/0.53  fof(f47,plain,(
% 1.38/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f22])).
% 1.38/0.53  fof(f22,plain,(
% 1.38/0.53    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.38/0.53    inference(ennf_transformation,[],[f3])).
% 1.38/0.53  fof(f3,axiom,(
% 1.38/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.38/0.53  fof(f175,plain,(
% 1.38/0.53    r1_xboole_0(k1_xboole_0,sK2)),
% 1.38/0.53    inference(resolution,[],[f170,f33])).
% 1.38/0.53  fof(f33,plain,(
% 1.38/0.53    r1_xboole_0(sK0,sK2)),
% 1.38/0.53    inference(cnf_transformation,[],[f26])).
% 1.38/0.53  fof(f277,plain,(
% 1.38/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.38/0.53    inference(superposition,[],[f267,f35])).
% 1.38/0.53  fof(f267,plain,(
% 1.38/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k4_xboole_0(X0,X0)) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 1.38/0.53    inference(superposition,[],[f53,f35])).
% 1.38/0.53  fof(f53,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.38/0.53    inference(definition_unfolding,[],[f43,f38])).
% 1.38/0.53  fof(f38,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f11])).
% 1.38/0.53  fof(f11,axiom,(
% 1.38/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.38/0.53  fof(f43,plain,(
% 1.38/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f28])).
% 1.38/0.53  fof(f28,plain,(
% 1.38/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.38/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f27])).
% 1.38/0.53  fof(f27,plain,(
% 1.38/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.38/0.53    introduced(choice_axiom,[])).
% 1.38/0.53  fof(f20,plain,(
% 1.38/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.38/0.53    inference(ennf_transformation,[],[f16])).
% 1.38/0.53  fof(f16,plain,(
% 1.38/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.38/0.53    inference(rectify,[],[f5])).
% 1.38/0.53  fof(f5,axiom,(
% 1.38/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.38/0.53  fof(f56,plain,(
% 1.38/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.38/0.53    inference(definition_unfolding,[],[f48,f38])).
% 1.38/0.53  fof(f48,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.38/0.53    inference(cnf_transformation,[],[f31])).
% 1.38/0.53  fof(f31,plain,(
% 1.38/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.38/0.53    inference(nnf_transformation,[],[f2])).
% 1.38/0.53  fof(f2,axiom,(
% 1.38/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.38/0.53  fof(f438,plain,(
% 1.38/0.53    ( ! [X10,X9] : (k4_xboole_0(X9,k2_xboole_0(X10,X9)) = k4_xboole_0(k2_xboole_0(X10,X9),k2_xboole_0(X10,X9))) )),
% 1.38/0.53    inference(superposition,[],[f41,f401])).
% 1.38/0.53  fof(f401,plain,(
% 1.38/0.53    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 1.38/0.53    inference(superposition,[],[f329,f37])).
% 1.38/0.53  fof(f329,plain,(
% 1.38/0.53    ( ! [X8,X9] : (k2_xboole_0(X8,X9) = k2_xboole_0(X8,k2_xboole_0(X8,X9))) )),
% 1.38/0.53    inference(forward_demodulation,[],[f323,f39])).
% 1.38/0.53  fof(f323,plain,(
% 1.38/0.53    ( ! [X8,X9] : (k2_xboole_0(X8,k2_xboole_0(X8,X9)) = k2_xboole_0(X8,k4_xboole_0(X9,X8))) )),
% 1.38/0.53    inference(superposition,[],[f39,f74])).
% 1.38/0.53  fof(f74,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 1.38/0.53    inference(superposition,[],[f41,f37])).
% 1.38/0.53  fof(f1876,plain,(
% 1.38/0.53    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)))),
% 1.38/0.53    inference(forward_demodulation,[],[f1874,f50])).
% 1.38/0.53  fof(f1874,plain,(
% 1.38/0.53    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK0))),
% 1.38/0.53    inference(resolution,[],[f1873,f56])).
% 1.38/0.53  fof(f1873,plain,(
% 1.38/0.53    r1_xboole_0(k4_xboole_0(sK0,sK1),sK0)),
% 1.38/0.53    inference(resolution,[],[f1849,f47])).
% 1.38/0.53  fof(f1849,plain,(
% 1.38/0.53    r1_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.38/0.53    inference(resolution,[],[f1807,f164])).
% 1.38/0.53  fof(f164,plain,(
% 1.38/0.53    ( ! [X0] : (~r1_xboole_0(k2_xboole_0(sK1,sK2),X0) | r1_xboole_0(sK0,X0)) )),
% 1.38/0.53    inference(resolution,[],[f51,f32])).
% 1.38/0.53  fof(f32,plain,(
% 1.38/0.53    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 1.38/0.53    inference(cnf_transformation,[],[f26])).
% 1.38/0.53  fof(f1807,plain,(
% 1.38/0.53    ( ! [X0] : (r1_xboole_0(k2_xboole_0(X0,sK2),k4_xboole_0(sK0,X0))) )),
% 1.38/0.53    inference(superposition,[],[f1749,f37])).
% 1.38/0.53  fof(f1749,plain,(
% 1.38/0.53    ( ! [X17] : (r1_xboole_0(k2_xboole_0(sK2,X17),k4_xboole_0(sK0,X17))) )),
% 1.38/0.53    inference(superposition,[],[f1025,f1699])).
% 1.38/0.53  fof(f1699,plain,(
% 1.38/0.53    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)) )),
% 1.38/0.53    inference(superposition,[],[f50,f1657])).
% 1.38/0.53  fof(f1657,plain,(
% 1.38/0.53    sK0 = k4_xboole_0(sK0,sK2)),
% 1.38/0.53    inference(forward_demodulation,[],[f1625,f35])).
% 1.38/0.53  fof(f1625,plain,(
% 1.38/0.53    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.38/0.53    inference(superposition,[],[f52,f944])).
% 1.38/0.53  fof(f944,plain,(
% 1.38/0.53    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.38/0.53    inference(resolution,[],[f56,f33])).
% 1.38/0.53  fof(f52,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.38/0.53    inference(definition_unfolding,[],[f40,f38])).
% 1.38/0.53  fof(f40,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f10])).
% 1.38/0.53  fof(f10,axiom,(
% 1.38/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.38/0.53  fof(f1025,plain,(
% 1.38/0.53    ( ! [X2,X3] : (r1_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 1.38/0.53    inference(resolution,[],[f975,f47])).
% 1.38/0.53  fof(f975,plain,(
% 1.38/0.53    ( ! [X8,X7] : (r1_xboole_0(k4_xboole_0(X7,X8),X8)) )),
% 1.38/0.53    inference(trivial_inequality_removal,[],[f974])).
% 1.38/0.53  fof(f974,plain,(
% 1.38/0.53    ( ! [X8,X7] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k4_xboole_0(X7,X8),X8)) )),
% 1.38/0.53    inference(backward_demodulation,[],[f686,f947])).
% 1.38/0.53  fof(f947,plain,(
% 1.38/0.53    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)) )),
% 1.38/0.53    inference(backward_demodulation,[],[f102,f946])).
% 1.38/0.53  fof(f102,plain,(
% 1.38/0.53    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X3,X3)) )),
% 1.38/0.53    inference(superposition,[],[f41,f87])).
% 1.38/0.53  fof(f686,plain,(
% 1.38/0.53    ( ! [X8,X7] : (k1_xboole_0 != k4_xboole_0(k1_xboole_0,k4_xboole_0(X7,X8)) | r1_xboole_0(k4_xboole_0(X7,X8),X8)) )),
% 1.38/0.53    inference(forward_demodulation,[],[f684,f102])).
% 1.38/0.53  fof(f684,plain,(
% 1.38/0.53    ( ! [X8,X7] : (k1_xboole_0 != k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,X8)) | r1_xboole_0(k4_xboole_0(X7,X8),X8)) )),
% 1.38/0.53    inference(superposition,[],[f55,f325])).
% 1.38/0.53  fof(f325,plain,(
% 1.38/0.53    ( ! [X6,X7] : (k4_xboole_0(X7,X6) = k4_xboole_0(k4_xboole_0(X7,X6),X6)) )),
% 1.38/0.53    inference(forward_demodulation,[],[f316,f74])).
% 1.38/0.53  fof(f316,plain,(
% 1.38/0.53    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X7,X6),X6) = k4_xboole_0(k2_xboole_0(X6,X7),X6)) )),
% 1.38/0.53    inference(superposition,[],[f74,f39])).
% 1.38/0.53  fof(f55,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.38/0.53    inference(definition_unfolding,[],[f49,f38])).
% 1.38/0.53  fof(f49,plain,(
% 1.38/0.53    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.38/0.53    inference(cnf_transformation,[],[f31])).
% 1.38/0.53  fof(f39,plain,(
% 1.38/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f6])).
% 1.38/0.53  fof(f6,axiom,(
% 1.38/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.38/0.53  fof(f59,plain,(
% 1.38/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 1.38/0.53    inference(superposition,[],[f36,f37])).
% 1.38/0.53  fof(f36,plain,(
% 1.38/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.38/0.53    inference(cnf_transformation,[],[f13])).
% 1.38/0.53  fof(f13,axiom,(
% 1.38/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.38/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.38/0.53  % SZS output end Proof for theBenchmark
% 1.38/0.53  % (26686)------------------------------
% 1.38/0.53  % (26686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (26686)Termination reason: Refutation
% 1.38/0.53  
% 1.38/0.53  % (26686)Memory used [KB]: 11385
% 1.38/0.53  % (26686)Time elapsed: 0.106 s
% 1.38/0.53  % (26686)------------------------------
% 1.38/0.53  % (26686)------------------------------
% 1.38/0.53  % (26676)Success in time 0.175 s
%------------------------------------------------------------------------------
