%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 295 expanded)
%              Number of leaves         :   21 (  96 expanded)
%              Depth                    :   22
%              Number of atoms          :  145 ( 376 expanded)
%              Number of equality atoms :   77 ( 285 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f390,plain,(
    $false ),
    inference(resolution,[],[f386,f74])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f386,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f96,f380])).

fof(f380,plain,(
    k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f70,f378])).

fof(f378,plain,(
    k1_xboole_0 = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f323,f331])).

fof(f331,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f329,f48])).

fof(f48,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f329,plain,(
    k3_tarski(k1_xboole_0) = sK0 ),
    inference(superposition,[],[f197,f323])).

fof(f197,plain,(
    ! [X1] : k3_tarski(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(forward_demodulation,[],[f196,f103])).

fof(f103,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(resolution,[],[f49,f74])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f196,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = k3_tarski(k2_enumset1(X1,X1,X1,X1)) ),
    inference(forward_demodulation,[],[f172,f79])).

fof(f79,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f53,f45])).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f172,plain,(
    ! [X1] : k3_tarski(k2_enumset1(X1,X1,X1,X1)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X1)) ),
    inference(superposition,[],[f68,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f68,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f40,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f323,plain,(
    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f322,f185])).

fof(f185,plain,(
    k1_xboole_0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f68,f78])).

fof(f78,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f77,f53])).

fof(f77,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f67,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f67,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f39,f40,f66])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f65])).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

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

fof(f322,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f321,f155])).

fof(f155,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(forward_demodulation,[],[f138,f79])).

fof(f138,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f52,f46])).

fof(f52,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f321,plain,(
    k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f318,f53])).

fof(f318,plain,(
    k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1) ),
    inference(superposition,[],[f68,f306])).

fof(f306,plain,(
    sK1 = k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f300,f49])).

fof(f300,plain,(
    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f91,f295])).

fof(f295,plain,(
    sK1 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f287,f45])).

fof(f287,plain,(
    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f155,f144])).

fof(f144,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f52,f78])).

fof(f91,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) ),
    inference(superposition,[],[f71,f51])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f62,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f70,plain,(
    k1_zfmisc_1(k1_xboole_0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f44,f66])).

fof(f44,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f96,plain,(
    ! [X4] : ~ r1_tarski(k1_zfmisc_1(X4),X4) ),
    inference(resolution,[],[f72,f76])).

fof(f76,plain,(
    ! [X0] : ~ r2_hidden(X0,X0) ),
    inference(factoring,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f72,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:17:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.45  % (12515)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (12515)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f390,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(resolution,[],[f386,f74])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.48    inference(equality_resolution,[],[f60])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.48    inference(flattening,[],[f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.48  fof(f386,plain,(
% 0.22/0.48    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.22/0.48    inference(superposition,[],[f96,f380])).
% 0.22/0.48  fof(f380,plain,(
% 0.22/0.48    k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)),
% 0.22/0.48    inference(backward_demodulation,[],[f70,f378])).
% 0.22/0.48  fof(f378,plain,(
% 0.22/0.48    k1_xboole_0 = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.48    inference(backward_demodulation,[],[f323,f331])).
% 0.22/0.48  fof(f331,plain,(
% 0.22/0.48    k1_xboole_0 = sK0),
% 0.22/0.48    inference(forward_demodulation,[],[f329,f48])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,axiom,(
% 0.22/0.48    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.22/0.48  fof(f329,plain,(
% 0.22/0.48    k3_tarski(k1_xboole_0) = sK0),
% 0.22/0.48    inference(superposition,[],[f197,f323])).
% 0.22/0.48  fof(f197,plain,(
% 0.22/0.48    ( ! [X1] : (k3_tarski(k2_enumset1(X1,X1,X1,X1)) = X1) )),
% 0.22/0.48    inference(forward_demodulation,[],[f196,f103])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 0.22/0.48    inference(resolution,[],[f49,f74])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.48  fof(f196,plain,(
% 0.22/0.48    ( ! [X1] : (k3_xboole_0(X1,X1) = k3_tarski(k2_enumset1(X1,X1,X1,X1))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f172,f79])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.22/0.48    inference(superposition,[],[f53,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.22/0.48  fof(f172,plain,(
% 0.22/0.48    ( ! [X1] : (k3_tarski(k2_enumset1(X1,X1,X1,X1)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X1))) )),
% 0.22/0.48    inference(superposition,[],[f68,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,axiom,(
% 0.22/0.48    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f41,f40,f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f54,f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,axiom,(
% 0.22/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.48  fof(f323,plain,(
% 0.22/0.48    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.48    inference(forward_demodulation,[],[f322,f185])).
% 0.22/0.48  fof(f185,plain,(
% 0.22/0.48    k1_xboole_0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.22/0.48    inference(superposition,[],[f68,f78])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.22/0.48    inference(backward_demodulation,[],[f77,f53])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.22/0.48    inference(backward_demodulation,[],[f67,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    k1_xboole_0 = k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 0.22/0.48    inference(definition_unfolding,[],[f39,f40,f66])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f43,f65])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,axiom,(
% 0.22/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.48    inference(ennf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.48    inference(negated_conjecture,[],[f25])).
% 0.22/0.48  fof(f25,conjecture,(
% 0.22/0.48    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.48  fof(f322,plain,(
% 0.22/0.48    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.22/0.48    inference(forward_demodulation,[],[f321,f155])).
% 0.22/0.48  fof(f155,plain,(
% 0.22/0.48    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 0.22/0.48    inference(forward_demodulation,[],[f138,f79])).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 0.22/0.48    inference(superposition,[],[f52,f46])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.48  fof(f321,plain,(
% 0.22/0.48    k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.22/0.48    inference(forward_demodulation,[],[f318,f53])).
% 0.22/0.48  fof(f318,plain,(
% 0.22/0.48    k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)),sK1)),
% 0.22/0.48    inference(superposition,[],[f68,f306])).
% 0.22/0.48  fof(f306,plain,(
% 0.22/0.48    sK1 = k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.48    inference(resolution,[],[f300,f49])).
% 0.22/0.48  fof(f300,plain,(
% 0.22/0.48    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.48    inference(superposition,[],[f91,f295])).
% 0.22/0.48  fof(f295,plain,(
% 0.22/0.48    sK1 = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.22/0.48    inference(forward_demodulation,[],[f287,f45])).
% 0.22/0.48  fof(f287,plain,(
% 0.22/0.48    k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k1_xboole_0)),
% 0.22/0.48    inference(superposition,[],[f155,f144])).
% 0.22/0.48  fof(f144,plain,(
% 0.22/0.48    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))))),
% 0.22/0.48    inference(superposition,[],[f52,f78])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0)) )),
% 0.22/0.48    inference(superposition,[],[f71,f51])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f62,f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    k1_zfmisc_1(k1_xboole_0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.48    inference(definition_unfolding,[],[f44,f66])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,axiom,(
% 0.22/0.48    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    ( ! [X4] : (~r1_tarski(k1_zfmisc_1(X4),X4)) )),
% 0.22/0.48    inference(resolution,[],[f72,f76])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,X0)) )),
% 0.22/0.48    inference(factoring,[],[f64])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.22/0.48    inference(equality_resolution,[],[f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.48    inference(rectify,[],[f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,axiom,(
% 0.22/0.48    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (12515)------------------------------
% 0.22/0.48  % (12515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (12515)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (12515)Memory used [KB]: 1918
% 0.22/0.48  % (12515)Time elapsed: 0.096 s
% 0.22/0.48  % (12515)------------------------------
% 0.22/0.48  % (12515)------------------------------
% 0.22/0.48  % (12509)Success in time 0.125 s
%------------------------------------------------------------------------------
