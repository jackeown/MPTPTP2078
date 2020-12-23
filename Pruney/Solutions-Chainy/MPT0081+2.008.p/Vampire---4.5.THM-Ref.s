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
% DateTime   : Thu Dec  3 12:31:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 355 expanded)
%              Number of leaves         :   13 ( 104 expanded)
%              Depth                    :   18
%              Number of atoms          :  129 ( 706 expanded)
%              Number of equality atoms :   40 ( 252 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f661,plain,(
    $false ),
    inference(resolution,[],[f643,f40])).

fof(f40,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f25,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( r1_xboole_0(sK0,sK1)
    & ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) )
   => ( r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f643,plain,(
    ! [X6] : r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X6))) ),
    inference(trivial_inequality_removal,[],[f630])).

fof(f630,plain,(
    ! [X6] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X6))) ) ),
    inference(superposition,[],[f47,f611])).

fof(f611,plain,(
    ! [X15] : k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X15)))) ),
    inference(forward_demodulation,[],[f610,f157])).

fof(f157,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f43,f86])).

fof(f86,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(resolution,[],[f48,f72])).

fof(f72,plain,(
    ! [X2] : r1_xboole_0(k1_xboole_0,X2) ),
    inference(resolution,[],[f69,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f63,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f45,f41])).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f29])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f29])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f69,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f47,f41])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f37,f29])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f610,plain,(
    ! [X15] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X15)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X15)))) ),
    inference(forward_demodulation,[],[f573,f300])).

fof(f300,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f84,f295])).

fof(f295,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f281,f109])).

fof(f109,plain,(
    ! [X3] : k2_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(superposition,[],[f42,f84])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f281,plain,(
    ! [X2] : k2_xboole_0(k4_xboole_0(X2,k1_xboole_0),k1_xboole_0) = X2 ),
    inference(superposition,[],[f44,f84])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f31,f29])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f48,f71])).

fof(f71,plain,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[],[f69,f65])).

fof(f65,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f63,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f573,plain,(
    ! [X15] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X15)))) = k4_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(k4_xboole_0(sK0,sK0),X15)) ),
    inference(superposition,[],[f49,f302])).

fof(f302,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f155,f295])).

fof(f155,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f43,f87])).

fof(f87,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f48,f26])).

fof(f26,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f39,f29,f29,f29,f29])).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f29])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:54:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (7024)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.44  % (7024)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f661,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(resolution,[],[f643,f40])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    ~r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.22/0.44    inference(definition_unfolding,[],[f25,f29])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,axiom,(
% 0.22/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.22/0.44    inference(cnf_transformation,[],[f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2))) => (r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.44    inference(ennf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.44    inference(negated_conjecture,[],[f10])).
% 0.22/0.44  fof(f10,conjecture,(
% 0.22/0.44    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).
% 0.22/0.44  fof(f643,plain,(
% 0.22/0.44    ( ! [X6] : (r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X6)))) )),
% 0.22/0.44    inference(trivial_inequality_removal,[],[f630])).
% 0.22/0.44  fof(f630,plain,(
% 0.22/0.44    ( ! [X6] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X6)))) )),
% 0.22/0.44    inference(superposition,[],[f47,f611])).
% 0.22/0.44  fof(f611,plain,(
% 0.22/0.44    ( ! [X15] : (k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X15))))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f610,f157])).
% 0.22/0.44  fof(f157,plain,(
% 0.22/0.44    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 0.22/0.44    inference(superposition,[],[f43,f86])).
% 0.22/0.44  fof(f86,plain,(
% 0.22/0.44    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) )),
% 0.22/0.44    inference(resolution,[],[f48,f72])).
% 0.22/0.44  fof(f72,plain,(
% 0.22/0.44    ( ! [X2] : (r1_xboole_0(k1_xboole_0,X2)) )),
% 0.22/0.44    inference(resolution,[],[f69,f64])).
% 0.22/0.44  fof(f64,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.44    inference(resolution,[],[f63,f34])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.45    inference(ennf_transformation,[],[f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.45    inference(rectify,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r1_xboole_0(X0,X0)) )),
% 0.22/0.45    inference(superposition,[],[f45,f41])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.22/0.45    inference(definition_unfolding,[],[f27,f29])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.45    inference(rectify,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.45    inference(definition_unfolding,[],[f33,f29])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.45    inference(ennf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.45    inference(rectify,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.45  fof(f69,plain,(
% 0.22/0.45    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.45    inference(equality_resolution,[],[f67])).
% 0.22/0.45  fof(f67,plain,(
% 0.22/0.45    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 0.22/0.45    inference(superposition,[],[f47,f41])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f37,f29])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f24])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.45    inference(nnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f30,f29])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.45  fof(f610,plain,(
% 0.22/0.45    ( ! [X15] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X15)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X15))))) )),
% 0.22/0.45    inference(forward_demodulation,[],[f573,f300])).
% 0.22/0.45  fof(f300,plain,(
% 0.22/0.45    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.45    inference(backward_demodulation,[],[f84,f295])).
% 0.22/0.45  fof(f295,plain,(
% 0.22/0.45    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 0.22/0.45    inference(superposition,[],[f281,f109])).
% 0.22/0.45  fof(f109,plain,(
% 0.22/0.45    ( ! [X3] : (k2_xboole_0(X3,k1_xboole_0) = X3) )),
% 0.22/0.45    inference(superposition,[],[f42,f84])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 0.22/0.45    inference(definition_unfolding,[],[f28,f29])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.22/0.45    inference(cnf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.22/0.45  fof(f281,plain,(
% 0.22/0.45    ( ! [X2] : (k2_xboole_0(k4_xboole_0(X2,k1_xboole_0),k1_xboole_0) = X2) )),
% 0.22/0.45    inference(superposition,[],[f44,f84])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.45    inference(definition_unfolding,[],[f31,f29])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.45    inference(cnf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,axiom,(
% 0.22/0.45    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.45  fof(f84,plain,(
% 0.22/0.45    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.45    inference(resolution,[],[f48,f71])).
% 0.22/0.45  fof(f71,plain,(
% 0.22/0.45    ( ! [X1] : (r1_xboole_0(X1,k1_xboole_0)) )),
% 0.22/0.45    inference(resolution,[],[f69,f65])).
% 0.22/0.45  fof(f65,plain,(
% 0.22/0.45    ( ! [X2,X3] : (~r1_xboole_0(X2,X2) | r1_xboole_0(X3,X2)) )),
% 0.22/0.45    inference(resolution,[],[f63,f35])).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f23])).
% 0.22/0.45  fof(f573,plain,(
% 0.22/0.45    ( ! [X15] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X15)))) = k4_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(k4_xboole_0(sK0,sK0),X15))) )),
% 0.22/0.45    inference(superposition,[],[f49,f302])).
% 0.22/0.45  fof(f302,plain,(
% 0.22/0.45    sK0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.45    inference(backward_demodulation,[],[f155,f295])).
% 0.22/0.45  fof(f155,plain,(
% 0.22/0.45    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.45    inference(superposition,[],[f43,f87])).
% 0.22/0.45  fof(f87,plain,(
% 0.22/0.45    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.22/0.45    inference(resolution,[],[f48,f26])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    r1_xboole_0(sK0,sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f19])).
% 0.22/0.45  fof(f49,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f39,f29,f29,f29,f29])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.22/0.45  fof(f47,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.45    inference(definition_unfolding,[],[f38,f29])).
% 0.22/0.45  fof(f38,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.45    inference(cnf_transformation,[],[f24])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (7024)------------------------------
% 0.22/0.45  % (7024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (7024)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (7024)Memory used [KB]: 1791
% 0.22/0.45  % (7024)Time elapsed: 0.017 s
% 0.22/0.45  % (7024)------------------------------
% 0.22/0.45  % (7024)------------------------------
% 0.22/0.45  % (7008)Success in time 0.086 s
%------------------------------------------------------------------------------
