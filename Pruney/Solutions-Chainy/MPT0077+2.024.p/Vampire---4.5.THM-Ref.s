%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:47 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   97 (1043 expanded)
%              Number of leaves         :   15 ( 283 expanded)
%              Depth                    :   26
%              Number of atoms          :  227 (3644 expanded)
%              Number of equality atoms :   36 ( 313 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1481,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1480,f808])).

fof(f808,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f806])).

fof(f806,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | ~ r2_hidden(X4,k1_xboole_0) ) ),
    inference(resolution,[],[f788,f51])).

fof(f51,plain,(
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
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f788,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(condensation,[],[f783])).

fof(f783,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(k1_xboole_0,X2)
      | r1_xboole_0(k1_xboole_0,X3) ) ),
    inference(backward_demodulation,[],[f596,f740])).

fof(f740,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f737,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f737,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f723,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f723,plain,
    ( r1_xboole_0(sK1,sK0)
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f170,f43])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f170,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_xboole_0(sK1,sK2))
      | r1_xboole_0(X0,sK0)
      | k1_xboole_0 = k3_xboole_0(sK0,sK1) ) ),
    inference(resolution,[],[f90,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f90,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f62,f53])).

fof(f62,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f40,f54])).

fof(f40,plain,
    ( r1_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_xboole_0(sK0,sK1) ) )
    | ( r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
        & ( ~ r1_xboole_0(sK0,sK2)
          | ~ r1_xboole_0(sK0,sK1) ) )
      | ( r1_xboole_0(sK0,sK2)
        & r1_xboole_0(sK0,sK1)
        & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f596,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(k3_xboole_0(sK0,sK1),X2)
      | r1_xboole_0(k1_xboole_0,X3) ) ),
    inference(resolution,[],[f579,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f579,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | r1_xboole_0(k3_xboole_0(sK0,sK1),X3) ) ),
    inference(subsumption_resolution,[],[f578,f96])).

fof(f96,plain,(
    ! [X1] :
      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      | r1_xboole_0(k3_xboole_0(sK0,sK1),X1) ) ),
    inference(resolution,[],[f65,f49])).

fof(f65,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k3_xboole_0(sK0,sK1))
      | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(resolution,[],[f40,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f578,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | r1_xboole_0(k3_xboole_0(sK0,sK1),X3)
      | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(superposition,[],[f186,f54])).

fof(f186,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
      | r1_xboole_0(k3_xboole_0(sK0,sK1),X6) ) ),
    inference(resolution,[],[f96,f48])).

fof(f1480,plain,(
    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1479,f1381])).

fof(f1381,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f1364,f54])).

fof(f1364,plain,
    ( r1_xboole_0(sK0,sK2)
    | k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f1137,f1284])).

fof(f1284,plain,(
    ! [X3] : k2_xboole_0(k1_xboole_0,X3) = X3 ),
    inference(resolution,[],[f1261,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1261,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f992,f42])).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f992,plain,(
    ! [X10,X9] : r1_tarski(k1_xboole_0,k2_xboole_0(X9,X10)) ),
    inference(forward_demodulation,[],[f987,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f987,plain,(
    ! [X10,X9] : r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X10)),k2_xboole_0(X9,X10)) ),
    inference(superposition,[],[f57,f804])).

fof(f804,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) ),
    inference(resolution,[],[f788,f54])).

fof(f57,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f1137,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2))
    | k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f1051,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1051,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2)))
      | k1_xboole_0 = k3_xboole_0(sK0,sK2) ) ),
    inference(backward_demodulation,[],[f103,f1045])).

fof(f1045,plain,(
    ! [X4] : k3_xboole_0(sK0,k2_xboole_0(sK1,X4)) = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X4)) ),
    inference(backward_demodulation,[],[f884,f1027])).

fof(f1027,plain,(
    ! [X14,X13] : k3_xboole_0(X13,k2_xboole_0(k1_xboole_0,X14)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X13,X14)) ),
    inference(superposition,[],[f58,f829])).

fof(f829,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0) ),
    inference(resolution,[],[f789,f54])).

fof(f789,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(condensation,[],[f773])).

fof(f773,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,k1_xboole_0)
      | r1_xboole_0(X1,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f562,f740])).

fof(f562,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(sK0,sK1))
      | r1_xboole_0(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f561,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f561,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | r1_xboole_0(X3,k3_xboole_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f560,f95])).

fof(f95,plain,(
    ! [X0] :
      ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      | r1_xboole_0(X0,k3_xboole_0(sK0,sK1)) ) ),
    inference(resolution,[],[f65,f50])).

fof(f560,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | r1_xboole_0(X3,k3_xboole_0(sK0,sK1))
      | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(superposition,[],[f180,f54])).

fof(f180,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
      | r1_xboole_0(X6,k3_xboole_0(sK0,sK1)) ) ),
    inference(resolution,[],[f95,f48])).

fof(f58,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f884,plain,(
    ! [X4] : k3_xboole_0(sK0,k2_xboole_0(sK1,X4)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X4)) ),
    inference(superposition,[],[f58,f740])).

fof(f103,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
      | k1_xboole_0 = k3_xboole_0(sK0,sK2) ) ),
    inference(resolution,[],[f67,f48])).

fof(f67,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f41,f54])).

fof(f41,plain,
    ( r1_xboole_0(sK0,sK2)
    | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f1479,plain,(
    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f1459,f1300])).

fof(f1300,plain,(
    ! [X4] : k3_xboole_0(sK0,X4) = k3_xboole_0(sK0,k2_xboole_0(sK1,X4)) ),
    inference(backward_demodulation,[],[f1045,f1284])).

fof(f1459,plain,(
    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f1444,f47])).

fof(f1444,plain,(
    ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1443,f889])).

fof(f889,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f878,f808])).

fof(f878,plain,
    ( r2_hidden(sK3(sK0,sK1),k1_xboole_0)
    | r1_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f47,f740])).

fof(f1443,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f1383])).

fof(f1383,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f73,f1381])).

fof(f73,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f36,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f36,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:09:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.48  % (26959)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.48  % (26950)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.48  % (26950)Refutation not found, incomplete strategy% (26950)------------------------------
% 0.20/0.48  % (26950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (26950)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (26950)Memory used [KB]: 10490
% 0.20/0.48  % (26950)Time elapsed: 0.056 s
% 0.20/0.48  % (26950)------------------------------
% 0.20/0.48  % (26950)------------------------------
% 0.20/0.49  % (26946)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.49  % (26944)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (26947)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.50  % (26945)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (26954)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.50  % (26963)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.51  % (26953)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.16/0.51  % (26945)Refutation not found, incomplete strategy% (26945)------------------------------
% 1.16/0.51  % (26945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.51  % (26945)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.51  
% 1.16/0.51  % (26945)Memory used [KB]: 10618
% 1.16/0.51  % (26945)Time elapsed: 0.093 s
% 1.16/0.51  % (26945)------------------------------
% 1.16/0.51  % (26945)------------------------------
% 1.16/0.51  % (26962)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.16/0.51  % (26948)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.16/0.51  % (26955)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.16/0.51  % (26962)Refutation not found, incomplete strategy% (26962)------------------------------
% 1.16/0.51  % (26962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.51  % (26956)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.16/0.51  % (26962)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.51  
% 1.16/0.51  % (26962)Memory used [KB]: 6140
% 1.16/0.51  % (26962)Time elapsed: 0.096 s
% 1.16/0.51  % (26962)------------------------------
% 1.16/0.51  % (26962)------------------------------
% 1.16/0.52  % (26964)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.16/0.52  % (26943)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.16/0.52  % (26958)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.16/0.52  % (26958)Refutation not found, incomplete strategy% (26958)------------------------------
% 1.16/0.52  % (26958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.52  % (26958)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.52  
% 1.16/0.52  % (26958)Memory used [KB]: 1663
% 1.16/0.52  % (26958)Time elapsed: 0.083 s
% 1.16/0.52  % (26958)------------------------------
% 1.16/0.52  % (26958)------------------------------
% 1.16/0.53  % (26952)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.16/0.53  % (26952)Refutation not found, incomplete strategy% (26952)------------------------------
% 1.16/0.53  % (26952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.53  % (26952)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.53  
% 1.16/0.53  % (26952)Memory used [KB]: 10490
% 1.16/0.53  % (26952)Time elapsed: 0.118 s
% 1.16/0.53  % (26952)------------------------------
% 1.16/0.53  % (26952)------------------------------
% 1.16/0.53  % (26965)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.36/0.53  % (26961)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.36/0.53  % (26957)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.36/0.54  % (26960)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.36/0.54  % (26942)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.36/0.54  % (26953)Refutation found. Thanks to Tanya!
% 1.36/0.54  % SZS status Theorem for theBenchmark
% 1.36/0.54  % SZS output start Proof for theBenchmark
% 1.36/0.54  fof(f1481,plain,(
% 1.36/0.54    $false),
% 1.36/0.54    inference(subsumption_resolution,[],[f1480,f808])).
% 1.36/0.54  fof(f808,plain,(
% 1.36/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.36/0.54    inference(condensation,[],[f806])).
% 1.36/0.54  fof(f806,plain,(
% 1.36/0.54    ( ! [X4,X5] : (~r2_hidden(X4,X5) | ~r2_hidden(X4,k1_xboole_0)) )),
% 1.36/0.54    inference(resolution,[],[f788,f51])).
% 1.36/0.54  fof(f51,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f34])).
% 1.36/0.54  fof(f34,plain,(
% 1.36/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f33])).
% 1.36/0.54  fof(f33,plain,(
% 1.36/0.54    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f23,plain,(
% 1.36/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.36/0.54    inference(ennf_transformation,[],[f20])).
% 1.36/0.54  fof(f20,plain,(
% 1.36/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.36/0.54    inference(rectify,[],[f4])).
% 1.36/0.54  fof(f4,axiom,(
% 1.36/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.36/0.54  fof(f788,plain,(
% 1.36/0.54    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.36/0.54    inference(condensation,[],[f783])).
% 1.36/0.54  fof(f783,plain,(
% 1.36/0.54    ( ! [X2,X3] : (r1_xboole_0(k1_xboole_0,X2) | r1_xboole_0(k1_xboole_0,X3)) )),
% 1.36/0.54    inference(backward_demodulation,[],[f596,f740])).
% 1.36/0.54  fof(f740,plain,(
% 1.36/0.54    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.36/0.54    inference(subsumption_resolution,[],[f737,f54])).
% 1.36/0.54  fof(f54,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f35])).
% 1.36/0.54  fof(f35,plain,(
% 1.36/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.36/0.54    inference(nnf_transformation,[],[f1])).
% 1.36/0.54  fof(f1,axiom,(
% 1.36/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.36/0.54  fof(f737,plain,(
% 1.36/0.54    k1_xboole_0 = k3_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)),
% 1.36/0.54    inference(resolution,[],[f723,f53])).
% 1.36/0.54  fof(f53,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f25])).
% 1.36/0.54  fof(f25,plain,(
% 1.36/0.54    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.36/0.54    inference(ennf_transformation,[],[f3])).
% 1.36/0.54  fof(f3,axiom,(
% 1.36/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.36/0.54  fof(f723,plain,(
% 1.36/0.54    r1_xboole_0(sK1,sK0) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.36/0.54    inference(resolution,[],[f170,f43])).
% 1.36/0.54  fof(f43,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f15])).
% 1.36/0.54  fof(f15,axiom,(
% 1.36/0.54    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.36/0.54  fof(f170,plain,(
% 1.36/0.54    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(X0,sK0) | k1_xboole_0 = k3_xboole_0(sK0,sK1)) )),
% 1.36/0.54    inference(resolution,[],[f90,f60])).
% 1.36/0.54  fof(f60,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f28])).
% 1.36/0.54  fof(f28,plain,(
% 1.36/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.36/0.54    inference(flattening,[],[f27])).
% 1.36/0.54  fof(f27,plain,(
% 1.36/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.36/0.54    inference(ennf_transformation,[],[f14])).
% 1.36/0.54  fof(f14,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.36/0.54  fof(f90,plain,(
% 1.36/0.54    r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.36/0.54    inference(resolution,[],[f62,f53])).
% 1.36/0.54  fof(f62,plain,(
% 1.36/0.54    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.36/0.54    inference(resolution,[],[f40,f54])).
% 1.36/0.54  fof(f40,plain,(
% 1.36/0.54    r1_xboole_0(sK0,sK1) | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.36/0.54    inference(cnf_transformation,[],[f30])).
% 1.36/0.54  fof(f30,plain,(
% 1.36/0.54    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f29])).
% 1.36/0.54  fof(f29,plain,(
% 1.36/0.54    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f21,plain,(
% 1.36/0.54    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.36/0.54    inference(ennf_transformation,[],[f17])).
% 1.36/0.54  fof(f17,negated_conjecture,(
% 1.36/0.54    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.36/0.54    inference(negated_conjecture,[],[f16])).
% 1.36/0.54  fof(f16,conjecture,(
% 1.36/0.54    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.36/0.54  fof(f596,plain,(
% 1.36/0.54    ( ! [X2,X3] : (r1_xboole_0(k3_xboole_0(sK0,sK1),X2) | r1_xboole_0(k1_xboole_0,X3)) )),
% 1.36/0.54    inference(resolution,[],[f579,f49])).
% 1.36/0.54  fof(f49,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f34])).
% 1.36/0.54  fof(f579,plain,(
% 1.36/0.54    ( ! [X2,X3] : (~r2_hidden(X2,k1_xboole_0) | r1_xboole_0(k3_xboole_0(sK0,sK1),X3)) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f578,f96])).
% 1.36/0.54  fof(f96,plain,(
% 1.36/0.54    ( ! [X1] : (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(k3_xboole_0(sK0,sK1),X1)) )),
% 1.36/0.54    inference(resolution,[],[f65,f49])).
% 1.36/0.54  fof(f65,plain,(
% 1.36/0.54    ( ! [X2] : (~r2_hidden(X2,k3_xboole_0(sK0,sK1)) | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))) )),
% 1.36/0.54    inference(resolution,[],[f40,f48])).
% 1.36/0.54  fof(f48,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f32])).
% 1.36/0.54  fof(f32,plain,(
% 1.36/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f31])).
% 1.36/0.54  fof(f31,plain,(
% 1.36/0.54    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f22,plain,(
% 1.36/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.36/0.54    inference(ennf_transformation,[],[f19])).
% 1.36/0.54  fof(f19,plain,(
% 1.36/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.36/0.54    inference(rectify,[],[f5])).
% 1.36/0.54  fof(f5,axiom,(
% 1.36/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.36/0.54  fof(f578,plain,(
% 1.36/0.54    ( ! [X2,X3] : (~r2_hidden(X2,k1_xboole_0) | r1_xboole_0(k3_xboole_0(sK0,sK1),X3) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))) )),
% 1.36/0.54    inference(superposition,[],[f186,f54])).
% 1.36/0.54  fof(f186,plain,(
% 1.36/0.54    ( ! [X6,X7] : (~r2_hidden(X7,k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | r1_xboole_0(k3_xboole_0(sK0,sK1),X6)) )),
% 1.36/0.54    inference(resolution,[],[f96,f48])).
% 1.36/0.54  fof(f1480,plain,(
% 1.36/0.54    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_xboole_0)),
% 1.36/0.54    inference(forward_demodulation,[],[f1479,f1381])).
% 1.36/0.54  fof(f1381,plain,(
% 1.36/0.54    k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 1.36/0.54    inference(subsumption_resolution,[],[f1364,f54])).
% 1.36/0.54  fof(f1364,plain,(
% 1.36/0.54    r1_xboole_0(sK0,sK2) | k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 1.36/0.54    inference(backward_demodulation,[],[f1137,f1284])).
% 1.36/0.54  fof(f1284,plain,(
% 1.36/0.54    ( ! [X3] : (k2_xboole_0(k1_xboole_0,X3) = X3) )),
% 1.36/0.54    inference(resolution,[],[f1261,f52])).
% 1.36/0.54  fof(f52,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f24])).
% 1.36/0.54  fof(f24,plain,(
% 1.36/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.36/0.54    inference(ennf_transformation,[],[f6])).
% 1.36/0.54  fof(f6,axiom,(
% 1.36/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.36/0.54  fof(f1261,plain,(
% 1.36/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.36/0.54    inference(superposition,[],[f992,f42])).
% 1.36/0.54  fof(f42,plain,(
% 1.36/0.54    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.36/0.54    inference(cnf_transformation,[],[f18])).
% 1.36/0.54  fof(f18,plain,(
% 1.36/0.54    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.36/0.54    inference(rectify,[],[f2])).
% 1.36/0.54  fof(f2,axiom,(
% 1.36/0.54    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.36/0.54  fof(f992,plain,(
% 1.36/0.54    ( ! [X10,X9] : (r1_tarski(k1_xboole_0,k2_xboole_0(X9,X10))) )),
% 1.36/0.54    inference(forward_demodulation,[],[f987,f45])).
% 1.36/0.54  fof(f45,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.36/0.54    inference(cnf_transformation,[],[f7])).
% 1.36/0.54  fof(f7,axiom,(
% 1.36/0.54    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.36/0.54  fof(f987,plain,(
% 1.36/0.54    ( ! [X10,X9] : (r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X10)),k2_xboole_0(X9,X10))) )),
% 1.36/0.54    inference(superposition,[],[f57,f804])).
% 1.36/0.54  fof(f804,plain,(
% 1.36/0.54    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) )),
% 1.36/0.54    inference(resolution,[],[f788,f54])).
% 1.36/0.54  fof(f57,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f10])).
% 1.36/0.54  fof(f10,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 1.36/0.54  fof(f1137,plain,(
% 1.36/0.54    r1_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2)) | k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 1.36/0.54    inference(resolution,[],[f1051,f47])).
% 1.36/0.54  fof(f47,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f32])).
% 1.36/0.54  fof(f1051,plain,(
% 1.36/0.54    ( ! [X2] : (~r2_hidden(X2,k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2))) | k1_xboole_0 = k3_xboole_0(sK0,sK2)) )),
% 1.36/0.54    inference(backward_demodulation,[],[f103,f1045])).
% 1.36/0.54  fof(f1045,plain,(
% 1.36/0.54    ( ! [X4] : (k3_xboole_0(sK0,k2_xboole_0(sK1,X4)) = k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X4))) )),
% 1.36/0.54    inference(backward_demodulation,[],[f884,f1027])).
% 1.36/0.54  fof(f1027,plain,(
% 1.36/0.54    ( ! [X14,X13] : (k3_xboole_0(X13,k2_xboole_0(k1_xboole_0,X14)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X13,X14))) )),
% 1.36/0.54    inference(superposition,[],[f58,f829])).
% 1.36/0.54  fof(f829,plain,(
% 1.36/0.54    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)) )),
% 1.36/0.54    inference(resolution,[],[f789,f54])).
% 1.36/0.54  fof(f789,plain,(
% 1.36/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.36/0.54    inference(condensation,[],[f773])).
% 1.36/0.54  fof(f773,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_xboole_0(X0,k1_xboole_0) | r1_xboole_0(X1,k1_xboole_0)) )),
% 1.36/0.54    inference(backward_demodulation,[],[f562,f740])).
% 1.36/0.54  fof(f562,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_xboole_0(X0,k3_xboole_0(sK0,sK1)) | r1_xboole_0(X1,k1_xboole_0)) )),
% 1.36/0.54    inference(resolution,[],[f561,f50])).
% 1.36/0.54  fof(f50,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f34])).
% 1.36/0.54  fof(f561,plain,(
% 1.36/0.54    ( ! [X2,X3] : (~r2_hidden(X2,k1_xboole_0) | r1_xboole_0(X3,k3_xboole_0(sK0,sK1))) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f560,f95])).
% 1.36/0.54  fof(f95,plain,(
% 1.36/0.54    ( ! [X0] : (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(X0,k3_xboole_0(sK0,sK1))) )),
% 1.36/0.54    inference(resolution,[],[f65,f50])).
% 1.36/0.54  fof(f560,plain,(
% 1.36/0.54    ( ! [X2,X3] : (~r2_hidden(X2,k1_xboole_0) | r1_xboole_0(X3,k3_xboole_0(sK0,sK1)) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))) )),
% 1.36/0.54    inference(superposition,[],[f180,f54])).
% 1.36/0.54  fof(f180,plain,(
% 1.36/0.54    ( ! [X6,X7] : (~r2_hidden(X7,k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | r1_xboole_0(X6,k3_xboole_0(sK0,sK1))) )),
% 1.36/0.54    inference(resolution,[],[f95,f48])).
% 1.36/0.54  fof(f58,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f8])).
% 1.36/0.54  fof(f8,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 1.36/0.54  fof(f884,plain,(
% 1.36/0.54    ( ! [X4] : (k3_xboole_0(sK0,k2_xboole_0(sK1,X4)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X4))) )),
% 1.36/0.54    inference(superposition,[],[f58,f740])).
% 1.36/0.54  fof(f103,plain,(
% 1.36/0.54    ( ! [X2] : (~r2_hidden(X2,k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | k1_xboole_0 = k3_xboole_0(sK0,sK2)) )),
% 1.36/0.54    inference(resolution,[],[f67,f48])).
% 1.36/0.54  fof(f67,plain,(
% 1.36/0.54    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 1.36/0.54    inference(resolution,[],[f41,f54])).
% 1.36/0.54  fof(f41,plain,(
% 1.36/0.54    r1_xboole_0(sK0,sK2) | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.36/0.54    inference(cnf_transformation,[],[f30])).
% 1.36/0.54  fof(f1479,plain,(
% 1.36/0.54    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,sK2))),
% 1.36/0.54    inference(forward_demodulation,[],[f1459,f1300])).
% 1.36/0.54  fof(f1300,plain,(
% 1.36/0.54    ( ! [X4] : (k3_xboole_0(sK0,X4) = k3_xboole_0(sK0,k2_xboole_0(sK1,X4))) )),
% 1.36/0.54    inference(backward_demodulation,[],[f1045,f1284])).
% 1.36/0.54  fof(f1459,plain,(
% 1.36/0.54    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 1.36/0.54    inference(resolution,[],[f1444,f47])).
% 1.36/0.54  fof(f1444,plain,(
% 1.36/0.54    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.36/0.54    inference(subsumption_resolution,[],[f1443,f889])).
% 1.36/0.54  fof(f889,plain,(
% 1.36/0.54    r1_xboole_0(sK0,sK1)),
% 1.36/0.54    inference(subsumption_resolution,[],[f878,f808])).
% 1.36/0.54  fof(f878,plain,(
% 1.36/0.54    r2_hidden(sK3(sK0,sK1),k1_xboole_0) | r1_xboole_0(sK0,sK1)),
% 1.36/0.54    inference(superposition,[],[f47,f740])).
% 1.36/0.54  fof(f1443,plain,(
% 1.36/0.54    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~r1_xboole_0(sK0,sK1)),
% 1.36/0.54    inference(trivial_inequality_removal,[],[f1383])).
% 1.36/0.54  fof(f1383,plain,(
% 1.36/0.54    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~r1_xboole_0(sK0,sK1)),
% 1.36/0.54    inference(backward_demodulation,[],[f73,f1381])).
% 1.36/0.54  fof(f73,plain,(
% 1.36/0.54    k1_xboole_0 != k3_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~r1_xboole_0(sK0,sK1)),
% 1.36/0.54    inference(resolution,[],[f36,f55])).
% 1.36/0.54  fof(f55,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.36/0.54    inference(cnf_transformation,[],[f35])).
% 1.36/0.54  fof(f36,plain,(
% 1.36/0.54    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.36/0.54    inference(cnf_transformation,[],[f30])).
% 1.36/0.54  % SZS output end Proof for theBenchmark
% 1.36/0.54  % (26953)------------------------------
% 1.36/0.54  % (26953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (26953)Termination reason: Refutation
% 1.36/0.54  
% 1.36/0.54  % (26953)Memory used [KB]: 2174
% 1.36/0.54  % (26953)Time elapsed: 0.131 s
% 1.36/0.54  % (26953)------------------------------
% 1.36/0.54  % (26953)------------------------------
% 1.36/0.55  % (26939)Success in time 0.177 s
%------------------------------------------------------------------------------
