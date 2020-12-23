%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:52 EST 2020

% Result     : Theorem 2.06s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 540 expanded)
%              Number of leaves         :   19 ( 160 expanded)
%              Depth                    :   24
%              Number of atoms          :  158 (1255 expanded)
%              Number of equality atoms :   89 ( 472 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1644,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1643,f35])).

fof(f35,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f1643,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f1631,f38])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f1631,plain,(
    sK2 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f709,f1627])).

fof(f1627,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f1617,f146])).

fof(f146,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f140,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f140,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f51,f71])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f54,f38])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f37,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1617,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f583,f1608])).

fof(f1608,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f1596,f89])).

fof(f89,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f81,f32])).

fof(f32,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f81,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f46,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f1596,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f1481,f32])).

fof(f1481,plain,(
    ! [X1] : k2_xboole_0(sK3,X1) = k2_xboole_0(sK3,k2_xboole_0(X1,sK3)) ),
    inference(superposition,[],[f1297,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f1297,plain,(
    ! [X0] : k2_xboole_0(sK3,X0) = k2_xboole_0(k2_xboole_0(sK3,X0),sK3) ),
    inference(forward_demodulation,[],[f1296,f39])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f1296,plain,(
    ! [X0] : k2_xboole_0(k2_xboole_0(sK3,X0),sK3) = k2_xboole_0(sK3,k2_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1291,f52])).

fof(f1291,plain,(
    ! [X0] : k2_xboole_0(k2_xboole_0(sK3,X0),sK3) = k2_xboole_0(k2_xboole_0(sK3,X0),k1_xboole_0) ),
    inference(superposition,[],[f45,f1227])).

fof(f1227,plain,(
    ! [X9] : k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK3,X9)) ),
    inference(backward_demodulation,[],[f550,f1157])).

fof(f1157,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(backward_demodulation,[],[f594,f146])).

fof(f594,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(sK2,k2_xboole_0(X2,sK2)) ),
    inference(superposition,[],[f531,f43])).

fof(f531,plain,(
    ! [X8] : k4_xboole_0(k1_xboole_0,X8) = k4_xboole_0(sK2,k2_xboole_0(sK2,X8)) ),
    inference(backward_demodulation,[],[f137,f524])).

fof(f524,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f476,f59])).

fof(f59,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f43,f39])).

fof(f476,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f56,f105])).

fof(f105,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f102,f70])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f67,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f50,f36])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f102,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))) ),
    inference(resolution,[],[f57,f33])).

fof(f33,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f49,f44])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
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

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f47,f44])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f137,plain,(
    ! [X8] : k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X8)) = k4_xboole_0(k1_xboole_0,X8) ),
    inference(superposition,[],[f51,f105])).

fof(f550,plain,(
    ! [X9] : k4_xboole_0(k1_xboole_0,X9) = k4_xboole_0(sK3,k2_xboole_0(sK3,X9)) ),
    inference(backward_demodulation,[],[f138,f542])).

fof(f542,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[],[f477,f59])).

fof(f477,plain,(
    sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f56,f107])).

fof(f107,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f103,f70])).

fof(f103,plain,(
    ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) ),
    inference(resolution,[],[f57,f34])).

fof(f34,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f138,plain,(
    ! [X9] : k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X9)) = k4_xboole_0(k1_xboole_0,X9) ),
    inference(superposition,[],[f51,f107])).

fof(f583,plain,(
    ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[],[f51,f573])).

fof(f573,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f475,f59])).

fof(f475,plain,(
    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f56,f410])).

fof(f410,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f55,f107])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f42,f44,f44])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f709,plain,(
    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f704,f38])).

fof(f704,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f55,f686])).

fof(f686,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f538,f603])).

fof(f603,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f589,f353])).

fof(f353,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK3) ),
    inference(forward_demodulation,[],[f343,f107])).

fof(f343,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k4_xboole_0(k1_xboole_0,sK3) ),
    inference(superposition,[],[f138,f115])).

fof(f115,plain,(
    k4_xboole_0(sK3,sK1) = k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) ),
    inference(forward_demodulation,[],[f114,f39])).

fof(f114,plain,(
    k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) ),
    inference(superposition,[],[f45,f107])).

fof(f589,plain,(
    k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f531,f32])).

fof(f538,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f51,f524])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:08:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (24129)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.50  % (24113)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (24121)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (24122)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (24112)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (24127)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (24109)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (24125)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (24126)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (24136)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (24137)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (24111)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (24115)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (24110)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (24118)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (24131)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (24114)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (24123)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (24124)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (24128)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (24124)Refutation not found, incomplete strategy% (24124)------------------------------
% 0.21/0.54  % (24124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24124)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24124)Memory used [KB]: 6140
% 0.21/0.54  % (24124)Time elapsed: 0.136 s
% 0.21/0.54  % (24124)------------------------------
% 0.21/0.54  % (24124)------------------------------
% 0.21/0.55  % (24138)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (24120)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (24119)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (24135)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (24132)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (24134)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (24130)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.56/0.55  % (24116)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.56/0.56  % (24126)Refutation not found, incomplete strategy% (24126)------------------------------
% 1.56/0.56  % (24126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.56  % (24126)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.56  
% 1.56/0.56  % (24126)Memory used [KB]: 10618
% 1.56/0.56  % (24126)Time elapsed: 0.147 s
% 1.56/0.56  % (24126)------------------------------
% 1.56/0.56  % (24126)------------------------------
% 1.56/0.56  % (24133)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.56/0.56  % (24117)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 2.06/0.63  % (24112)Refutation found. Thanks to Tanya!
% 2.06/0.63  % SZS status Theorem for theBenchmark
% 2.06/0.63  % SZS output start Proof for theBenchmark
% 2.06/0.63  fof(f1644,plain,(
% 2.06/0.63    $false),
% 2.06/0.63    inference(subsumption_resolution,[],[f1643,f35])).
% 2.06/0.63  fof(f35,plain,(
% 2.06/0.63    sK1 != sK2),
% 2.06/0.63    inference(cnf_transformation,[],[f25])).
% 2.06/0.63  fof(f25,plain,(
% 2.06/0.63    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.06/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f24])).
% 2.06/0.63  fof(f24,plain,(
% 2.06/0.63    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 2.06/0.63    introduced(choice_axiom,[])).
% 2.06/0.63  fof(f21,plain,(
% 2.06/0.63    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 2.06/0.63    inference(flattening,[],[f20])).
% 2.06/0.63  fof(f20,plain,(
% 2.06/0.63    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 2.06/0.63    inference(ennf_transformation,[],[f18])).
% 2.06/0.63  fof(f18,negated_conjecture,(
% 2.06/0.63    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.06/0.63    inference(negated_conjecture,[],[f17])).
% 2.06/0.63  fof(f17,conjecture,(
% 2.06/0.63    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 2.06/0.63  fof(f1643,plain,(
% 2.06/0.63    sK1 = sK2),
% 2.06/0.63    inference(forward_demodulation,[],[f1631,f38])).
% 2.06/0.63  fof(f38,plain,(
% 2.06/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.06/0.63    inference(cnf_transformation,[],[f9])).
% 2.06/0.63  fof(f9,axiom,(
% 2.06/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.06/0.63  fof(f1631,plain,(
% 2.06/0.63    sK2 = k4_xboole_0(sK1,k1_xboole_0)),
% 2.06/0.63    inference(backward_demodulation,[],[f709,f1627])).
% 2.06/0.63  fof(f1627,plain,(
% 2.06/0.63    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 2.06/0.63    inference(forward_demodulation,[],[f1617,f146])).
% 2.06/0.63  fof(f146,plain,(
% 2.06/0.63    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 2.06/0.63    inference(forward_demodulation,[],[f140,f45])).
% 2.06/0.63  fof(f45,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f8])).
% 2.06/0.63  fof(f8,axiom,(
% 2.06/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.06/0.63  fof(f140,plain,(
% 2.06/0.63    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 2.06/0.63    inference(superposition,[],[f51,f71])).
% 2.06/0.63  fof(f71,plain,(
% 2.06/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.06/0.63    inference(forward_demodulation,[],[f54,f38])).
% 2.06/0.63  fof(f54,plain,(
% 2.06/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.06/0.63    inference(definition_unfolding,[],[f37,f44])).
% 2.06/0.63  fof(f44,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f12])).
% 2.06/0.63  fof(f12,axiom,(
% 2.06/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.06/0.63  fof(f37,plain,(
% 2.06/0.63    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f7])).
% 2.06/0.63  fof(f7,axiom,(
% 2.06/0.63    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.06/0.63  fof(f51,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f10])).
% 2.06/0.63  fof(f10,axiom,(
% 2.06/0.63    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.06/0.63  fof(f1617,plain,(
% 2.06/0.63    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 2.06/0.63    inference(superposition,[],[f583,f1608])).
% 2.06/0.63  fof(f1608,plain,(
% 2.06/0.63    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2)),
% 2.06/0.63    inference(forward_demodulation,[],[f1596,f89])).
% 2.06/0.63  fof(f89,plain,(
% 2.06/0.63    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.06/0.63    inference(superposition,[],[f81,f32])).
% 2.06/0.63  fof(f32,plain,(
% 2.06/0.63    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.06/0.63    inference(cnf_transformation,[],[f25])).
% 2.06/0.63  fof(f81,plain,(
% 2.06/0.63    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 2.06/0.63    inference(superposition,[],[f46,f43])).
% 2.06/0.63  fof(f43,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f1])).
% 2.06/0.63  fof(f1,axiom,(
% 2.06/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.06/0.63  fof(f46,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f15])).
% 2.06/0.63  fof(f15,axiom,(
% 2.06/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 2.06/0.63  fof(f1596,plain,(
% 2.06/0.63    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.06/0.63    inference(superposition,[],[f1481,f32])).
% 2.06/0.63  fof(f1481,plain,(
% 2.06/0.63    ( ! [X1] : (k2_xboole_0(sK3,X1) = k2_xboole_0(sK3,k2_xboole_0(X1,sK3))) )),
% 2.06/0.63    inference(superposition,[],[f1297,f52])).
% 2.06/0.63  fof(f52,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f13])).
% 2.06/0.63  fof(f13,axiom,(
% 2.06/0.63    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 2.06/0.63  fof(f1297,plain,(
% 2.06/0.63    ( ! [X0] : (k2_xboole_0(sK3,X0) = k2_xboole_0(k2_xboole_0(sK3,X0),sK3)) )),
% 2.06/0.63    inference(forward_demodulation,[],[f1296,f39])).
% 2.06/0.63  fof(f39,plain,(
% 2.06/0.63    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.06/0.63    inference(cnf_transformation,[],[f6])).
% 2.06/0.63  fof(f6,axiom,(
% 2.06/0.63    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.06/0.63  fof(f1296,plain,(
% 2.06/0.63    ( ! [X0] : (k2_xboole_0(k2_xboole_0(sK3,X0),sK3) = k2_xboole_0(sK3,k2_xboole_0(X0,k1_xboole_0))) )),
% 2.06/0.63    inference(forward_demodulation,[],[f1291,f52])).
% 2.06/0.63  fof(f1291,plain,(
% 2.06/0.63    ( ! [X0] : (k2_xboole_0(k2_xboole_0(sK3,X0),sK3) = k2_xboole_0(k2_xboole_0(sK3,X0),k1_xboole_0)) )),
% 2.06/0.63    inference(superposition,[],[f45,f1227])).
% 2.06/0.63  fof(f1227,plain,(
% 2.06/0.63    ( ! [X9] : (k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK3,X9))) )),
% 2.06/0.63    inference(backward_demodulation,[],[f550,f1157])).
% 2.06/0.63  fof(f1157,plain,(
% 2.06/0.63    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 2.06/0.63    inference(backward_demodulation,[],[f594,f146])).
% 2.06/0.63  fof(f594,plain,(
% 2.06/0.63    ( ! [X2] : (k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(sK2,k2_xboole_0(X2,sK2))) )),
% 2.06/0.63    inference(superposition,[],[f531,f43])).
% 2.06/0.63  fof(f531,plain,(
% 2.06/0.63    ( ! [X8] : (k4_xboole_0(k1_xboole_0,X8) = k4_xboole_0(sK2,k2_xboole_0(sK2,X8))) )),
% 2.06/0.63    inference(backward_demodulation,[],[f137,f524])).
% 2.06/0.63  fof(f524,plain,(
% 2.06/0.63    sK2 = k4_xboole_0(sK2,sK0)),
% 2.06/0.63    inference(superposition,[],[f476,f59])).
% 2.06/0.63  fof(f59,plain,(
% 2.06/0.63    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.06/0.63    inference(superposition,[],[f43,f39])).
% 2.06/0.63  fof(f476,plain,(
% 2.06/0.63    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0))),
% 2.06/0.63    inference(superposition,[],[f56,f105])).
% 2.06/0.63  fof(f105,plain,(
% 2.06/0.63    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 2.06/0.63    inference(resolution,[],[f102,f70])).
% 2.06/0.63  fof(f70,plain,(
% 2.06/0.63    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 2.06/0.63    inference(resolution,[],[f67,f41])).
% 2.06/0.63  fof(f41,plain,(
% 2.06/0.63    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f29])).
% 2.06/0.63  fof(f29,plain,(
% 2.06/0.63    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.06/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).
% 2.06/0.63  fof(f28,plain,(
% 2.06/0.63    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 2.06/0.63    introduced(choice_axiom,[])).
% 2.06/0.63  fof(f27,plain,(
% 2.06/0.63    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.06/0.63    inference(rectify,[],[f26])).
% 2.06/0.63  fof(f26,plain,(
% 2.06/0.63    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.06/0.63    inference(nnf_transformation,[],[f3])).
% 2.06/0.63  fof(f3,axiom,(
% 2.06/0.63    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.06/0.63  fof(f67,plain,(
% 2.06/0.63    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 2.06/0.63    inference(resolution,[],[f50,f36])).
% 2.06/0.63  fof(f36,plain,(
% 2.06/0.63    v1_xboole_0(k1_xboole_0)),
% 2.06/0.63    inference(cnf_transformation,[],[f4])).
% 2.06/0.63  fof(f4,axiom,(
% 2.06/0.63    v1_xboole_0(k1_xboole_0)),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.06/0.63  fof(f50,plain,(
% 2.06/0.63    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f23])).
% 2.06/0.63  fof(f23,plain,(
% 2.06/0.63    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.06/0.63    inference(ennf_transformation,[],[f16])).
% 2.06/0.63  fof(f16,axiom,(
% 2.06/0.63    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 2.06/0.63  fof(f102,plain,(
% 2.06/0.63    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)))) )),
% 2.06/0.63    inference(resolution,[],[f57,f33])).
% 2.06/0.63  fof(f33,plain,(
% 2.06/0.63    r1_xboole_0(sK2,sK0)),
% 2.06/0.63    inference(cnf_transformation,[],[f25])).
% 2.06/0.63  fof(f57,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.06/0.63    inference(definition_unfolding,[],[f49,f44])).
% 2.06/0.63  fof(f49,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f31])).
% 2.06/0.63  fof(f31,plain,(
% 2.06/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.06/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f30])).
% 2.06/0.63  fof(f30,plain,(
% 2.06/0.63    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 2.06/0.63    introduced(choice_axiom,[])).
% 2.06/0.63  fof(f22,plain,(
% 2.06/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.06/0.63    inference(ennf_transformation,[],[f19])).
% 2.06/0.63  fof(f19,plain,(
% 2.06/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.06/0.63    inference(rectify,[],[f5])).
% 2.06/0.63  fof(f5,axiom,(
% 2.06/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.06/0.63  fof(f56,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 2.06/0.63    inference(definition_unfolding,[],[f47,f44])).
% 2.06/0.63  fof(f47,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.06/0.63    inference(cnf_transformation,[],[f14])).
% 2.06/0.63  fof(f14,axiom,(
% 2.06/0.63    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.06/0.63  fof(f137,plain,(
% 2.06/0.63    ( ! [X8] : (k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X8)) = k4_xboole_0(k1_xboole_0,X8)) )),
% 2.06/0.63    inference(superposition,[],[f51,f105])).
% 2.06/0.63  fof(f550,plain,(
% 2.06/0.63    ( ! [X9] : (k4_xboole_0(k1_xboole_0,X9) = k4_xboole_0(sK3,k2_xboole_0(sK3,X9))) )),
% 2.06/0.63    inference(backward_demodulation,[],[f138,f542])).
% 2.06/0.63  fof(f542,plain,(
% 2.06/0.63    sK3 = k4_xboole_0(sK3,sK1)),
% 2.06/0.63    inference(superposition,[],[f477,f59])).
% 2.06/0.63  fof(f477,plain,(
% 2.06/0.63    sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1))),
% 2.06/0.63    inference(superposition,[],[f56,f107])).
% 2.06/0.63  fof(f107,plain,(
% 2.06/0.63    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 2.06/0.63    inference(resolution,[],[f103,f70])).
% 2.06/0.63  fof(f103,plain,(
% 2.06/0.63    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)))) )),
% 2.06/0.63    inference(resolution,[],[f57,f34])).
% 2.06/0.63  fof(f34,plain,(
% 2.06/0.63    r1_xboole_0(sK3,sK1)),
% 2.06/0.63    inference(cnf_transformation,[],[f25])).
% 2.06/0.63  fof(f138,plain,(
% 2.06/0.63    ( ! [X9] : (k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X9)) = k4_xboole_0(k1_xboole_0,X9)) )),
% 2.06/0.63    inference(superposition,[],[f51,f107])).
% 2.06/0.63  fof(f583,plain,(
% 2.06/0.63    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0)) )),
% 2.06/0.63    inference(superposition,[],[f51,f573])).
% 2.06/0.63  fof(f573,plain,(
% 2.06/0.63    sK1 = k4_xboole_0(sK1,sK3)),
% 2.06/0.63    inference(superposition,[],[f475,f59])).
% 2.06/0.63  fof(f475,plain,(
% 2.06/0.63    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))),
% 2.06/0.63    inference(superposition,[],[f56,f410])).
% 2.06/0.63  fof(f410,plain,(
% 2.06/0.63    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 2.06/0.63    inference(superposition,[],[f55,f107])).
% 2.06/0.63  fof(f55,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.06/0.63    inference(definition_unfolding,[],[f42,f44,f44])).
% 2.06/0.63  fof(f42,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f2])).
% 2.06/0.63  fof(f2,axiom,(
% 2.06/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.06/0.63  fof(f709,plain,(
% 2.06/0.63    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.06/0.63    inference(forward_demodulation,[],[f704,f38])).
% 2.06/0.63  fof(f704,plain,(
% 2.06/0.63    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.06/0.63    inference(superposition,[],[f55,f686])).
% 2.06/0.63  fof(f686,plain,(
% 2.06/0.63    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 2.06/0.63    inference(superposition,[],[f538,f603])).
% 2.06/0.63  fof(f603,plain,(
% 2.06/0.63    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 2.06/0.63    inference(forward_demodulation,[],[f589,f353])).
% 2.06/0.63  fof(f353,plain,(
% 2.06/0.63    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK3)),
% 2.06/0.63    inference(forward_demodulation,[],[f343,f107])).
% 2.06/0.63  fof(f343,plain,(
% 2.06/0.63    k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k4_xboole_0(k1_xboole_0,sK3)),
% 2.06/0.63    inference(superposition,[],[f138,f115])).
% 2.06/0.63  fof(f115,plain,(
% 2.06/0.63    k4_xboole_0(sK3,sK1) = k2_xboole_0(k4_xboole_0(sK3,sK1),sK3)),
% 2.06/0.63    inference(forward_demodulation,[],[f114,f39])).
% 2.06/0.63  fof(f114,plain,(
% 2.06/0.63    k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0)),
% 2.06/0.63    inference(superposition,[],[f45,f107])).
% 2.06/0.63  fof(f589,plain,(
% 2.06/0.63    k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 2.06/0.63    inference(superposition,[],[f531,f32])).
% 2.06/0.63  fof(f538,plain,(
% 2.06/0.63    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0)) )),
% 2.06/0.63    inference(superposition,[],[f51,f524])).
% 2.06/0.63  % SZS output end Proof for theBenchmark
% 2.06/0.63  % (24112)------------------------------
% 2.06/0.63  % (24112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.63  % (24112)Termination reason: Refutation
% 2.06/0.63  
% 2.06/0.63  % (24112)Memory used [KB]: 11769
% 2.06/0.63  % (24112)Time elapsed: 0.224 s
% 2.06/0.63  % (24112)------------------------------
% 2.06/0.63  % (24112)------------------------------
% 2.06/0.64  % (24108)Success in time 0.279 s
%------------------------------------------------------------------------------
