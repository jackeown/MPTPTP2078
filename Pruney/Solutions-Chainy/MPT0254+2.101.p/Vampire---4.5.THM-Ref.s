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

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 412 expanded)
%              Number of leaves         :   21 ( 132 expanded)
%              Depth                    :   18
%              Number of atoms          :  159 ( 497 expanded)
%              Number of equality atoms :   83 ( 384 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f624,plain,(
    $false ),
    inference(resolution,[],[f619,f448])).

fof(f448,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f426,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f426,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f48,f253])).

fof(f253,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k3_xboole_0(X7,X8) ),
    inference(backward_demodulation,[],[f135,f239])).

fof(f239,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f231,f53])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f231,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f207,f78])).

fof(f78,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f50,f46])).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f207,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f63,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f63,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f135,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k5_xboole_0(X7,k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f96,f94])).

fof(f94,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k3_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(resolution,[],[f57,f48])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f96,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f53,f49])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f619,plain,(
    ! [X0] : ~ r1_tarski(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f616,f92])).

fof(f92,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f91,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f91,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f56,f42])).

fof(f42,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f616,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_xboole_0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(backward_demodulation,[],[f86,f613])).

fof(f613,plain,(
    k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    inference(backward_demodulation,[],[f604,f612])).

fof(f612,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f611,f40])).

fof(f40,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f611,plain,(
    k3_tarski(k1_xboole_0) = sK0 ),
    inference(superposition,[],[f193,f604])).

fof(f193,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(backward_demodulation,[],[f90,f192])).

fof(f192,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f191,f106])).

fof(f106,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f105,f57])).

fof(f105,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f48,f101])).

fof(f101,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f95,f46])).

fof(f95,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f53,f44])).

fof(f191,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k3_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f172,f78])).

fof(f172,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f54,f45])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f90,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) ),
    inference(superposition,[],[f51,f47])).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f604,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f597,f102])).

fof(f102,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5) ),
    inference(forward_demodulation,[],[f98,f45])).

fof(f98,plain,(
    ! [X5] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X5) ),
    inference(superposition,[],[f53,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f49,f44])).

fof(f597,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f578,f595])).

fof(f595,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f590,f39])).

fof(f39,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f31])).

fof(f31,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f590,plain,(
    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f276,f578])).

fof(f276,plain,(
    ! [X10,X9] : k2_xboole_0(k4_xboole_0(X9,X10),X9) = X9 ),
    inference(backward_demodulation,[],[f206,f275])).

fof(f275,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k4_xboole_0(X5,X6)) = X5 ),
    inference(backward_demodulation,[],[f252,f260])).

fof(f260,plain,(
    ! [X6,X5] : k5_xboole_0(k3_xboole_0(X5,X6),k4_xboole_0(X5,X6)) = X5 ),
    inference(superposition,[],[f237,f53])).

fof(f237,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f231,f50])).

fof(f252,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k4_xboole_0(X5,X6)) = k5_xboole_0(k3_xboole_0(X5,X6),k4_xboole_0(X5,X6)) ),
    inference(backward_demodulation,[],[f183,f239])).

fof(f183,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k4_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(X5,X6)),k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f54,f115])).

fof(f115,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k3_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f94,f49])).

fof(f206,plain,(
    ! [X10,X9] : k2_xboole_0(k4_xboole_0(X9,X10),X9) = k2_xboole_0(X9,k4_xboole_0(X9,X10)) ),
    inference(forward_demodulation,[],[f205,f183])).

fof(f205,plain,(
    ! [X10,X9] : k2_xboole_0(k4_xboole_0(X9,X10),X9) = k5_xboole_0(k5_xboole_0(X9,k4_xboole_0(X9,X10)),k4_xboole_0(X9,X10)) ),
    inference(forward_demodulation,[],[f186,f50])).

fof(f186,plain,(
    ! [X10,X9] : k2_xboole_0(k4_xboole_0(X9,X10),X9) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X9,X10),X9),k4_xboole_0(X9,X10)) ),
    inference(superposition,[],[f54,f94])).

fof(f578,plain,(
    k1_tarski(sK0) = k4_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f555,f46])).

fof(f555,plain,(
    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    inference(superposition,[],[f354,f39])).

fof(f354,plain,(
    ! [X10,X9] : k4_xboole_0(X10,X9) = k5_xboole_0(X9,k2_xboole_0(X9,X10)) ),
    inference(superposition,[],[f231,f234])).

fof(f234,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f216,f96])).

fof(f216,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f63,f54])).

fof(f86,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_tarski(k1_xboole_0))
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f68,f41])).

fof(f41,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f68,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
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

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:18:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (3368)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (3363)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (3360)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (3356)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (3361)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (3371)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (3372)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (3382)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (3372)Refutation not found, incomplete strategy% (3372)------------------------------
% 0.22/0.53  % (3372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (3377)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (3372)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (3372)Memory used [KB]: 6140
% 0.22/0.53  % (3372)Time elapsed: 0.005 s
% 0.22/0.53  % (3372)------------------------------
% 0.22/0.53  % (3372)------------------------------
% 0.22/0.53  % (3387)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (3377)Refutation not found, incomplete strategy% (3377)------------------------------
% 0.22/0.53  % (3377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (3377)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (3377)Memory used [KB]: 10746
% 0.22/0.53  % (3377)Time elapsed: 0.118 s
% 0.22/0.53  % (3377)------------------------------
% 0.22/0.53  % (3377)------------------------------
% 0.22/0.53  % (3367)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (3367)Refutation not found, incomplete strategy% (3367)------------------------------
% 0.22/0.53  % (3367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (3367)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (3367)Memory used [KB]: 10618
% 0.22/0.53  % (3367)Time elapsed: 0.110 s
% 0.22/0.53  % (3367)------------------------------
% 0.22/0.53  % (3367)------------------------------
% 0.22/0.53  % (3380)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (3362)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (3369)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (3384)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (3381)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (3381)Refutation not found, incomplete strategy% (3381)------------------------------
% 0.22/0.54  % (3381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (3381)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (3381)Memory used [KB]: 1663
% 0.22/0.54  % (3381)Time elapsed: 0.110 s
% 0.22/0.54  % (3381)------------------------------
% 0.22/0.54  % (3381)------------------------------
% 0.22/0.54  % (3357)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (3364)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (3373)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (3359)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (3386)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (3379)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (3375)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (3374)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (3365)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (3374)Refutation not found, incomplete strategy% (3374)------------------------------
% 0.22/0.55  % (3374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (3374)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (3374)Memory used [KB]: 10618
% 0.22/0.55  % (3374)Time elapsed: 0.136 s
% 0.22/0.55  % (3374)------------------------------
% 0.22/0.55  % (3374)------------------------------
% 0.22/0.55  % (3383)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (3370)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (3388)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.56  % (3366)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.57  % (3361)Refutation not found, incomplete strategy% (3361)------------------------------
% 0.22/0.57  % (3361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (3376)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.58  % (3361)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (3361)Memory used [KB]: 6524
% 0.22/0.58  % (3361)Time elapsed: 0.155 s
% 0.22/0.58  % (3361)------------------------------
% 0.22/0.58  % (3361)------------------------------
% 1.68/0.59  % (3364)Refutation found. Thanks to Tanya!
% 1.68/0.59  % SZS status Theorem for theBenchmark
% 1.68/0.59  % SZS output start Proof for theBenchmark
% 1.68/0.59  fof(f624,plain,(
% 1.68/0.59    $false),
% 1.68/0.59    inference(resolution,[],[f619,f448])).
% 1.68/0.59  fof(f448,plain,(
% 1.68/0.59    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 1.68/0.59    inference(superposition,[],[f426,f49])).
% 1.68/0.59  fof(f49,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f1])).
% 1.68/0.59  fof(f1,axiom,(
% 1.68/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.68/0.59  fof(f426,plain,(
% 1.68/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.68/0.59    inference(superposition,[],[f48,f253])).
% 1.68/0.59  fof(f253,plain,(
% 1.68/0.59    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k3_xboole_0(X7,X8)) )),
% 1.68/0.59    inference(backward_demodulation,[],[f135,f239])).
% 1.68/0.59  fof(f239,plain,(
% 1.68/0.59    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 1.68/0.59    inference(superposition,[],[f231,f53])).
% 1.68/0.59  fof(f53,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.68/0.59    inference(cnf_transformation,[],[f4])).
% 1.68/0.59  fof(f4,axiom,(
% 1.68/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.68/0.59  fof(f231,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.68/0.59    inference(forward_demodulation,[],[f207,f78])).
% 1.68/0.59  fof(f78,plain,(
% 1.68/0.59    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.68/0.59    inference(superposition,[],[f50,f46])).
% 1.68/0.59  fof(f46,plain,(
% 1.68/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.68/0.59    inference(cnf_transformation,[],[f9])).
% 1.68/0.59  fof(f9,axiom,(
% 1.68/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.68/0.59  fof(f50,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f2])).
% 1.68/0.59  fof(f2,axiom,(
% 1.68/0.59    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.68/0.59  fof(f207,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.68/0.59    inference(superposition,[],[f63,f45])).
% 1.68/0.59  fof(f45,plain,(
% 1.68/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f12])).
% 1.68/0.59  fof(f12,axiom,(
% 1.68/0.59    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.68/0.59  fof(f63,plain,(
% 1.68/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.68/0.59    inference(cnf_transformation,[],[f11])).
% 1.68/0.59  fof(f11,axiom,(
% 1.68/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.68/0.59  fof(f135,plain,(
% 1.68/0.59    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k5_xboole_0(X7,k4_xboole_0(X7,X8))) )),
% 1.68/0.59    inference(superposition,[],[f96,f94])).
% 1.68/0.59  fof(f94,plain,(
% 1.68/0.59    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k3_xboole_0(k4_xboole_0(X1,X2),X1)) )),
% 1.68/0.59    inference(resolution,[],[f57,f48])).
% 1.68/0.59  fof(f57,plain,(
% 1.68/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.68/0.59    inference(cnf_transformation,[],[f30])).
% 1.68/0.59  fof(f30,plain,(
% 1.68/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.68/0.59    inference(ennf_transformation,[],[f5])).
% 1.68/0.59  fof(f5,axiom,(
% 1.68/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.68/0.59  fof(f96,plain,(
% 1.68/0.59    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 1.68/0.59    inference(superposition,[],[f53,f49])).
% 1.68/0.59  fof(f48,plain,(
% 1.68/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f8])).
% 1.68/0.59  fof(f8,axiom,(
% 1.68/0.59    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.68/0.59  fof(f619,plain,(
% 1.68/0.59    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0)) )),
% 1.68/0.59    inference(subsumption_resolution,[],[f616,f92])).
% 1.68/0.59  fof(f92,plain,(
% 1.68/0.59    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.68/0.59    inference(forward_demodulation,[],[f91,f44])).
% 1.68/0.59  fof(f44,plain,(
% 1.68/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f6])).
% 1.68/0.59  fof(f6,axiom,(
% 1.68/0.59    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.68/0.59  fof(f91,plain,(
% 1.68/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 1.68/0.59    inference(resolution,[],[f56,f42])).
% 1.68/0.59  fof(f42,plain,(
% 1.68/0.59    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f10])).
% 1.68/0.59  fof(f10,axiom,(
% 1.68/0.59    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.68/0.59  fof(f56,plain,(
% 1.68/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.68/0.59    inference(cnf_transformation,[],[f34])).
% 1.68/0.59  fof(f34,plain,(
% 1.68/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.68/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f33])).
% 1.68/0.59  fof(f33,plain,(
% 1.68/0.59    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 1.68/0.59    introduced(choice_axiom,[])).
% 1.68/0.59  fof(f29,plain,(
% 1.68/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.68/0.59    inference(ennf_transformation,[],[f27])).
% 1.68/0.59  fof(f27,plain,(
% 1.68/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.68/0.59    inference(rectify,[],[f3])).
% 1.68/0.59  fof(f3,axiom,(
% 1.68/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.68/0.59  fof(f616,plain,(
% 1.68/0.59    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.68/0.59    inference(backward_demodulation,[],[f86,f613])).
% 1.68/0.59  fof(f613,plain,(
% 1.68/0.59    k1_xboole_0 = k1_tarski(k1_xboole_0)),
% 1.68/0.59    inference(backward_demodulation,[],[f604,f612])).
% 1.68/0.59  fof(f612,plain,(
% 1.68/0.59    k1_xboole_0 = sK0),
% 1.68/0.59    inference(forward_demodulation,[],[f611,f40])).
% 1.68/0.59  fof(f40,plain,(
% 1.68/0.59    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.68/0.59    inference(cnf_transformation,[],[f24])).
% 1.68/0.59  fof(f24,axiom,(
% 1.68/0.59    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 1.68/0.59  fof(f611,plain,(
% 1.68/0.59    k3_tarski(k1_xboole_0) = sK0),
% 1.68/0.59    inference(superposition,[],[f193,f604])).
% 1.68/0.59  fof(f193,plain,(
% 1.68/0.59    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 1.68/0.59    inference(backward_demodulation,[],[f90,f192])).
% 1.68/0.59  fof(f192,plain,(
% 1.68/0.59    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.68/0.59    inference(forward_demodulation,[],[f191,f106])).
% 1.68/0.59  fof(f106,plain,(
% 1.68/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.68/0.59    inference(resolution,[],[f105,f57])).
% 1.68/0.59  fof(f105,plain,(
% 1.68/0.59    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.68/0.59    inference(superposition,[],[f48,f101])).
% 1.68/0.59  fof(f101,plain,(
% 1.68/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.68/0.59    inference(forward_demodulation,[],[f95,f46])).
% 1.68/0.59  fof(f95,plain,(
% 1.68/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 1.68/0.59    inference(superposition,[],[f53,f44])).
% 1.68/0.59  fof(f191,plain,(
% 1.68/0.59    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_xboole_0(X0,X0)) )),
% 1.68/0.59    inference(forward_demodulation,[],[f172,f78])).
% 1.68/0.59  fof(f172,plain,(
% 1.68/0.59    ( ! [X0] : (k2_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0))) )),
% 1.68/0.59    inference(superposition,[],[f54,f45])).
% 1.68/0.59  fof(f54,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.68/0.59    inference(cnf_transformation,[],[f13])).
% 1.68/0.59  fof(f13,axiom,(
% 1.68/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.68/0.59  fof(f90,plain,(
% 1.68/0.59    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))) )),
% 1.68/0.59    inference(superposition,[],[f51,f47])).
% 1.68/0.59  fof(f47,plain,(
% 1.68/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.68/0.59    inference(cnf_transformation,[],[f14])).
% 1.68/0.59  fof(f14,axiom,(
% 1.68/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.68/0.59  fof(f51,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.68/0.59    inference(cnf_transformation,[],[f22])).
% 1.68/0.59  fof(f22,axiom,(
% 1.68/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.68/0.59  fof(f604,plain,(
% 1.68/0.59    k1_xboole_0 = k1_tarski(sK0)),
% 1.68/0.59    inference(forward_demodulation,[],[f597,f102])).
% 1.68/0.59  fof(f102,plain,(
% 1.68/0.59    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)) )),
% 1.68/0.59    inference(forward_demodulation,[],[f98,f45])).
% 1.68/0.59  fof(f98,plain,(
% 1.68/0.59    ( ! [X5] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X5)) )),
% 1.68/0.59    inference(superposition,[],[f53,f70])).
% 1.68/0.59  fof(f70,plain,(
% 1.68/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.68/0.59    inference(superposition,[],[f49,f44])).
% 1.68/0.59  fof(f597,plain,(
% 1.68/0.59    k1_tarski(sK0) = k4_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 1.68/0.59    inference(backward_demodulation,[],[f578,f595])).
% 1.68/0.59  fof(f595,plain,(
% 1.68/0.59    k1_xboole_0 = sK1),
% 1.68/0.59    inference(forward_demodulation,[],[f590,f39])).
% 1.68/0.59  fof(f39,plain,(
% 1.68/0.59    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.68/0.59    inference(cnf_transformation,[],[f32])).
% 1.68/0.59  fof(f32,plain,(
% 1.68/0.59    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.68/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f31])).
% 1.68/0.59  fof(f31,plain,(
% 1.68/0.59    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.68/0.59    introduced(choice_axiom,[])).
% 1.68/0.59  fof(f28,plain,(
% 1.68/0.59    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 1.68/0.59    inference(ennf_transformation,[],[f26])).
% 1.68/0.59  fof(f26,negated_conjecture,(
% 1.68/0.59    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.68/0.59    inference(negated_conjecture,[],[f25])).
% 1.68/0.59  fof(f25,conjecture,(
% 1.68/0.59    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.68/0.59  fof(f590,plain,(
% 1.68/0.59    sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.68/0.59    inference(superposition,[],[f276,f578])).
% 1.68/0.59  fof(f276,plain,(
% 1.68/0.59    ( ! [X10,X9] : (k2_xboole_0(k4_xboole_0(X9,X10),X9) = X9) )),
% 1.68/0.59    inference(backward_demodulation,[],[f206,f275])).
% 1.68/0.59  fof(f275,plain,(
% 1.68/0.59    ( ! [X6,X5] : (k2_xboole_0(X5,k4_xboole_0(X5,X6)) = X5) )),
% 1.68/0.59    inference(backward_demodulation,[],[f252,f260])).
% 1.68/0.59  fof(f260,plain,(
% 1.68/0.59    ( ! [X6,X5] : (k5_xboole_0(k3_xboole_0(X5,X6),k4_xboole_0(X5,X6)) = X5) )),
% 1.68/0.59    inference(superposition,[],[f237,f53])).
% 1.68/0.59  fof(f237,plain,(
% 1.68/0.59    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 1.68/0.59    inference(superposition,[],[f231,f50])).
% 1.68/0.59  fof(f252,plain,(
% 1.68/0.59    ( ! [X6,X5] : (k2_xboole_0(X5,k4_xboole_0(X5,X6)) = k5_xboole_0(k3_xboole_0(X5,X6),k4_xboole_0(X5,X6))) )),
% 1.68/0.59    inference(backward_demodulation,[],[f183,f239])).
% 1.68/0.59  fof(f183,plain,(
% 1.68/0.59    ( ! [X6,X5] : (k2_xboole_0(X5,k4_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,k4_xboole_0(X5,X6)),k4_xboole_0(X5,X6))) )),
% 1.68/0.59    inference(superposition,[],[f54,f115])).
% 1.68/0.59  fof(f115,plain,(
% 1.68/0.59    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k3_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 1.68/0.59    inference(superposition,[],[f94,f49])).
% 1.68/0.59  fof(f206,plain,(
% 1.68/0.59    ( ! [X10,X9] : (k2_xboole_0(k4_xboole_0(X9,X10),X9) = k2_xboole_0(X9,k4_xboole_0(X9,X10))) )),
% 1.68/0.59    inference(forward_demodulation,[],[f205,f183])).
% 1.68/0.59  fof(f205,plain,(
% 1.68/0.59    ( ! [X10,X9] : (k2_xboole_0(k4_xboole_0(X9,X10),X9) = k5_xboole_0(k5_xboole_0(X9,k4_xboole_0(X9,X10)),k4_xboole_0(X9,X10))) )),
% 1.68/0.59    inference(forward_demodulation,[],[f186,f50])).
% 1.68/0.59  fof(f186,plain,(
% 1.68/0.59    ( ! [X10,X9] : (k2_xboole_0(k4_xboole_0(X9,X10),X9) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X9,X10),X9),k4_xboole_0(X9,X10))) )),
% 1.68/0.59    inference(superposition,[],[f54,f94])).
% 1.68/0.59  fof(f578,plain,(
% 1.68/0.59    k1_tarski(sK0) = k4_xboole_0(sK1,k1_tarski(sK0))),
% 1.68/0.59    inference(forward_demodulation,[],[f555,f46])).
% 1.68/0.59  fof(f555,plain,(
% 1.68/0.59    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 1.68/0.59    inference(superposition,[],[f354,f39])).
% 1.68/0.59  fof(f354,plain,(
% 1.68/0.59    ( ! [X10,X9] : (k4_xboole_0(X10,X9) = k5_xboole_0(X9,k2_xboole_0(X9,X10))) )),
% 1.68/0.59    inference(superposition,[],[f231,f234])).
% 1.68/0.59  fof(f234,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.68/0.59    inference(forward_demodulation,[],[f216,f96])).
% 1.68/0.59  fof(f216,plain,(
% 1.68/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 1.68/0.59    inference(superposition,[],[f63,f54])).
% 1.68/0.59  fof(f86,plain,(
% 1.68/0.59    ( ! [X0] : (r2_hidden(X0,k1_tarski(k1_xboole_0)) | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.68/0.59    inference(superposition,[],[f68,f41])).
% 1.68/0.59  fof(f41,plain,(
% 1.68/0.59    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.68/0.59    inference(cnf_transformation,[],[f23])).
% 1.68/0.59  fof(f23,axiom,(
% 1.68/0.59    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 1.68/0.59  fof(f68,plain,(
% 1.68/0.59    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.68/0.59    inference(equality_resolution,[],[f59])).
% 1.68/0.59  fof(f59,plain,(
% 1.68/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.68/0.59    inference(cnf_transformation,[],[f38])).
% 1.68/0.59  fof(f38,plain,(
% 1.68/0.59    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.68/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 1.68/0.59  fof(f37,plain,(
% 1.68/0.59    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.68/0.59    introduced(choice_axiom,[])).
% 1.68/0.59  fof(f36,plain,(
% 1.68/0.59    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.68/0.59    inference(rectify,[],[f35])).
% 1.68/0.59  fof(f35,plain,(
% 1.68/0.59    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.68/0.59    inference(nnf_transformation,[],[f21])).
% 1.68/0.59  fof(f21,axiom,(
% 1.68/0.59    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.68/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.68/0.59  % SZS output end Proof for theBenchmark
% 1.68/0.59  % (3364)------------------------------
% 1.68/0.59  % (3364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.59  % (3364)Termination reason: Refutation
% 1.68/0.59  
% 1.68/0.59  % (3364)Memory used [KB]: 6652
% 1.68/0.59  % (3364)Time elapsed: 0.137 s
% 1.68/0.59  % (3364)------------------------------
% 1.68/0.59  % (3364)------------------------------
% 1.68/0.59  % (3353)Success in time 0.225 s
%------------------------------------------------------------------------------
