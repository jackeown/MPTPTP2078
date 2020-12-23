%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 374 expanded)
%              Number of leaves         :   23 ( 119 expanded)
%              Depth                    :   18
%              Number of atoms          :  162 ( 462 expanded)
%              Number of equality atoms :   82 ( 345 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f816,plain,(
    $false ),
    inference(resolution,[],[f811,f84])).

fof(f84,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f51,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f811,plain,(
    ! [X0] : ~ r1_tarski(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f808,f108])).

fof(f108,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f107,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f107,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f59,f44])).

fof(f44,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f808,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f102,f805])).

fof(f805,plain,(
    k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    inference(backward_demodulation,[],[f796,f804])).

fof(f804,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f803,f42])).

fof(f42,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f803,plain,(
    k3_tarski(k1_xboole_0) = sK0 ),
    inference(superposition,[],[f379,f796])).

fof(f379,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(backward_demodulation,[],[f106,f378])).

fof(f378,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f377,f125])).

fof(f125,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f123,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f123,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f50,f119])).

fof(f119,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f113,f47])).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f113,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f56,f45])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f377,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k3_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f354,f94])).

fof(f94,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f53,f47])).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f354,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f57,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f106,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) ),
    inference(superposition,[],[f54,f48])).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f796,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f789,f74])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f49,f50])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f789,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f770,f787])).

fof(f787,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f782,f41])).

fof(f41,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f33])).

fof(f33,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f782,plain,(
    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f472,f770])).

fof(f472,plain,(
    ! [X17,X16] : k2_xboole_0(k4_xboole_0(X16,X17),X16) = X16 ),
    inference(backward_demodulation,[],[f400,f471])).

fof(f471,plain,(
    ! [X10,X9] : k2_xboole_0(X9,k4_xboole_0(X9,X10)) = X9 ),
    inference(backward_demodulation,[],[f448,f456])).

fof(f456,plain,(
    ! [X6,X5] : k5_xboole_0(k3_xboole_0(X5,X6),k4_xboole_0(X5,X6)) = X5 ),
    inference(superposition,[],[f433,f56])).

fof(f433,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f427,f53])).

fof(f427,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f403,f94])).

fof(f403,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f66,f46])).

fof(f66,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f448,plain,(
    ! [X10,X9] : k2_xboole_0(X9,k4_xboole_0(X9,X10)) = k5_xboole_0(k3_xboole_0(X9,X10),k4_xboole_0(X9,X10)) ),
    inference(backward_demodulation,[],[f367,f435])).

fof(f435,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f427,f56])).

fof(f367,plain,(
    ! [X10,X9] : k2_xboole_0(X9,k4_xboole_0(X9,X10)) = k5_xboole_0(k5_xboole_0(X9,k4_xboole_0(X9,X10)),k4_xboole_0(X9,X10)) ),
    inference(superposition,[],[f57,f135])).

fof(f135,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k3_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f109,f52])).

fof(f109,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f60,f50])).

fof(f400,plain,(
    ! [X17,X16] : k2_xboole_0(k4_xboole_0(X16,X17),X16) = k2_xboole_0(X16,k4_xboole_0(X16,X17)) ),
    inference(forward_demodulation,[],[f399,f367])).

fof(f399,plain,(
    ! [X17,X16] : k2_xboole_0(k4_xboole_0(X16,X17),X16) = k5_xboole_0(k5_xboole_0(X16,k4_xboole_0(X16,X17)),k4_xboole_0(X16,X17)) ),
    inference(forward_demodulation,[],[f371,f53])).

fof(f371,plain,(
    ! [X17,X16] : k2_xboole_0(k4_xboole_0(X16,X17),X16) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X16,X17),X16),k4_xboole_0(X16,X17)) ),
    inference(superposition,[],[f57,f109])).

fof(f770,plain,(
    k1_tarski(sK0) = k4_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f747,f47])).

fof(f747,plain,(
    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    inference(superposition,[],[f618,f41])).

fof(f618,plain,(
    ! [X10,X9] : k4_xboole_0(X10,X9) = k5_xboole_0(X9,k2_xboole_0(X9,X10)) ),
    inference(superposition,[],[f427,f430])).

fof(f430,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f412,f114])).

fof(f114,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f56,f52])).

fof(f412,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f66,f57])).

fof(f102,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_tarski(k1_xboole_0))
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f71,f43])).

fof(f43,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f71,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:32:35 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (21605)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.47  % (21597)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.47  % (21605)Refutation not found, incomplete strategy% (21605)------------------------------
% 0.22/0.47  % (21605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (21605)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (21605)Memory used [KB]: 6140
% 0.22/0.47  % (21605)Time elapsed: 0.004 s
% 0.22/0.47  % (21605)------------------------------
% 0.22/0.47  % (21605)------------------------------
% 0.22/0.50  % (21597)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f816,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(resolution,[],[f811,f84])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 0.22/0.50    inference(superposition,[],[f51,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.50  fof(f811,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f808,f108])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f107,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 0.22/0.50    inference(resolution,[],[f59,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    inference(rectify,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.50  fof(f808,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(backward_demodulation,[],[f102,f805])).
% 0.22/0.50  fof(f805,plain,(
% 0.22/0.50    k1_xboole_0 = k1_tarski(k1_xboole_0)),
% 0.22/0.50    inference(backward_demodulation,[],[f796,f804])).
% 0.22/0.50  fof(f804,plain,(
% 0.22/0.50    k1_xboole_0 = sK0),
% 0.22/0.50    inference(forward_demodulation,[],[f803,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,axiom,(
% 0.22/0.50    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.22/0.50  fof(f803,plain,(
% 0.22/0.50    k3_tarski(k1_xboole_0) = sK0),
% 0.22/0.50    inference(superposition,[],[f379,f796])).
% 0.22/0.50  fof(f379,plain,(
% 0.22/0.50    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 0.22/0.50    inference(backward_demodulation,[],[f106,f378])).
% 0.22/0.50  fof(f378,plain,(
% 0.22/0.50    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.50    inference(forward_demodulation,[],[f377,f125])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.50    inference(resolution,[],[f123,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.50    inference(superposition,[],[f50,f119])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.50    inference(forward_demodulation,[],[f113,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(superposition,[],[f56,f45])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.50  fof(f377,plain,(
% 0.22/0.50    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_xboole_0(X0,X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f354,f94])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.22/0.50    inference(superposition,[],[f53,f47])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.22/0.50  fof(f354,plain,(
% 0.22/0.50    ( ! [X0] : (k2_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0))) )),
% 0.22/0.50    inference(superposition,[],[f57,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))) )),
% 0.22/0.50    inference(superposition,[],[f54,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,axiom,(
% 0.22/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.50  fof(f796,plain,(
% 0.22/0.50    k1_xboole_0 = k1_tarski(sK0)),
% 0.22/0.50    inference(forward_demodulation,[],[f789,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(resolution,[],[f49,f50])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.50  fof(f789,plain,(
% 0.22/0.50    k1_tarski(sK0) = k4_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 0.22/0.50    inference(backward_demodulation,[],[f770,f787])).
% 0.22/0.50  fof(f787,plain,(
% 0.22/0.50    k1_xboole_0 = sK1),
% 0.22/0.50    inference(forward_demodulation,[],[f782,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.50    inference(ennf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.50    inference(negated_conjecture,[],[f26])).
% 0.22/0.50  fof(f26,conjecture,(
% 0.22/0.50    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.50  fof(f782,plain,(
% 0.22/0.50    sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.22/0.50    inference(superposition,[],[f472,f770])).
% 0.22/0.50  fof(f472,plain,(
% 0.22/0.50    ( ! [X17,X16] : (k2_xboole_0(k4_xboole_0(X16,X17),X16) = X16) )),
% 0.22/0.50    inference(backward_demodulation,[],[f400,f471])).
% 0.22/0.50  fof(f471,plain,(
% 0.22/0.50    ( ! [X10,X9] : (k2_xboole_0(X9,k4_xboole_0(X9,X10)) = X9) )),
% 0.22/0.50    inference(backward_demodulation,[],[f448,f456])).
% 0.22/0.50  fof(f456,plain,(
% 0.22/0.50    ( ! [X6,X5] : (k5_xboole_0(k3_xboole_0(X5,X6),k4_xboole_0(X5,X6)) = X5) )),
% 0.22/0.50    inference(superposition,[],[f433,f56])).
% 0.22/0.50  fof(f433,plain,(
% 0.22/0.50    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 0.22/0.50    inference(superposition,[],[f427,f53])).
% 0.22/0.50  fof(f427,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.22/0.50    inference(forward_demodulation,[],[f403,f94])).
% 0.22/0.50  fof(f403,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(superposition,[],[f66,f46])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.50  fof(f448,plain,(
% 0.22/0.50    ( ! [X10,X9] : (k2_xboole_0(X9,k4_xboole_0(X9,X10)) = k5_xboole_0(k3_xboole_0(X9,X10),k4_xboole_0(X9,X10))) )),
% 0.22/0.50    inference(backward_demodulation,[],[f367,f435])).
% 0.22/0.50  fof(f435,plain,(
% 0.22/0.50    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 0.22/0.50    inference(superposition,[],[f427,f56])).
% 0.22/0.50  fof(f367,plain,(
% 0.22/0.50    ( ! [X10,X9] : (k2_xboole_0(X9,k4_xboole_0(X9,X10)) = k5_xboole_0(k5_xboole_0(X9,k4_xboole_0(X9,X10)),k4_xboole_0(X9,X10))) )),
% 0.22/0.50    inference(superposition,[],[f57,f135])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k3_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 0.22/0.50    inference(superposition,[],[f109,f52])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.50    inference(resolution,[],[f60,f50])).
% 0.22/0.50  fof(f400,plain,(
% 0.22/0.50    ( ! [X17,X16] : (k2_xboole_0(k4_xboole_0(X16,X17),X16) = k2_xboole_0(X16,k4_xboole_0(X16,X17))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f399,f367])).
% 0.22/0.50  fof(f399,plain,(
% 0.22/0.50    ( ! [X17,X16] : (k2_xboole_0(k4_xboole_0(X16,X17),X16) = k5_xboole_0(k5_xboole_0(X16,k4_xboole_0(X16,X17)),k4_xboole_0(X16,X17))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f371,f53])).
% 0.22/0.50  fof(f371,plain,(
% 0.22/0.50    ( ! [X17,X16] : (k2_xboole_0(k4_xboole_0(X16,X17),X16) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X16,X17),X16),k4_xboole_0(X16,X17))) )),
% 0.22/0.50    inference(superposition,[],[f57,f109])).
% 0.22/0.50  fof(f770,plain,(
% 0.22/0.50    k1_tarski(sK0) = k4_xboole_0(sK1,k1_tarski(sK0))),
% 0.22/0.50    inference(forward_demodulation,[],[f747,f47])).
% 0.22/0.50  fof(f747,plain,(
% 0.22/0.50    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 0.22/0.50    inference(superposition,[],[f618,f41])).
% 0.22/0.50  fof(f618,plain,(
% 0.22/0.50    ( ! [X10,X9] : (k4_xboole_0(X10,X9) = k5_xboole_0(X9,k2_xboole_0(X9,X10))) )),
% 0.22/0.50    inference(superposition,[],[f427,f430])).
% 0.22/0.50  fof(f430,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f412,f114])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 0.22/0.50    inference(superposition,[],[f56,f52])).
% 0.22/0.50  fof(f412,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 0.22/0.50    inference(superposition,[],[f66,f57])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(X0,k1_tarski(k1_xboole_0)) | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(superposition,[],[f71,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,axiom,(
% 0.22/0.50    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.50    inference(rectify,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,axiom,(
% 0.22/0.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (21597)------------------------------
% 0.22/0.50  % (21597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (21597)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (21597)Memory used [KB]: 6780
% 0.22/0.50  % (21597)Time elapsed: 0.086 s
% 0.22/0.50  % (21597)------------------------------
% 0.22/0.50  % (21597)------------------------------
% 0.22/0.51  % (21589)Success in time 0.141 s
%------------------------------------------------------------------------------
