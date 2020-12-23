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
% DateTime   : Thu Dec  3 12:37:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 470 expanded)
%              Number of leaves         :   15 ( 140 expanded)
%              Depth                    :   13
%              Number of atoms          :  148 (1684 expanded)
%              Number of equality atoms :  107 (1522 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f416,plain,(
    $false ),
    inference(subsumption_resolution,[],[f415,f413])).

fof(f413,plain,(
    k1_xboole_0 != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f402,f410])).

fof(f410,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f398,f402])).

fof(f398,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k1_tarski(sK0) ),
    inference(resolution,[],[f396,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f396,plain,(
    r1_tarski(sK2,k1_tarski(sK0)) ),
    inference(superposition,[],[f370,f36])).

fof(f36,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f370,plain,(
    ! [X4,X5] : r1_tarski(X4,k2_xboole_0(X5,X4)) ),
    inference(superposition,[],[f44,f332])).

fof(f332,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f321,f225])).

fof(f225,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f210,f113])).

fof(f113,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f49,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f210,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f59,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f59,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f321,plain,(
    ! [X4,X3] : k5_xboole_0(X3,k4_xboole_0(X4,X3)) = k2_xboole_0(X4,X3) ),
    inference(forward_demodulation,[],[f298,f49])).

fof(f298,plain,(
    ! [X4,X3] : k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))) = k2_xboole_0(X4,X3) ),
    inference(superposition,[],[f154,f59])).

fof(f154,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f50,f46])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f402,plain,(
    sK2 != k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f38,f401])).

fof(f401,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f37,f179,f196,f398])).

fof(f196,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f189])).

fof(f189,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f39,f179])).

fof(f39,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f179,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f53,f68])).

fof(f68,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f44,f36])).

fof(f37,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f38,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f415,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f414,f410])).

fof(f414,plain,(
    sK2 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f403,f171])).

fof(f171,plain,(
    ! [X9] : k2_xboole_0(k1_xboole_0,X9) = X9 ),
    inference(forward_demodulation,[],[f170,f119])).

fof(f119,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = X4 ),
    inference(forward_demodulation,[],[f115,f41])).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f115,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f49,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f80,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f80,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(resolution,[],[f52,f40])).

fof(f40,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f170,plain,(
    ! [X9] : k2_xboole_0(k1_xboole_0,X9) = k4_xboole_0(X9,k1_xboole_0) ),
    inference(forward_demodulation,[],[f158,f113])).

fof(f158,plain,(
    ! [X9] : k2_xboole_0(k1_xboole_0,X9) = k5_xboole_0(X9,k3_xboole_0(k1_xboole_0,X9)) ),
    inference(superposition,[],[f50,f69])).

fof(f69,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f46,f41])).

fof(f403,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f36,f401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:22:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (22373)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (22373)Refutation not found, incomplete strategy% (22373)------------------------------
% 0.21/0.50  % (22373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22365)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (22373)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22373)Memory used [KB]: 6140
% 0.21/0.51  % (22373)Time elapsed: 0.006 s
% 0.21/0.51  % (22373)------------------------------
% 0.21/0.51  % (22373)------------------------------
% 0.21/0.53  % (22365)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 1.24/0.53  % SZS output start Proof for theBenchmark
% 1.24/0.53  fof(f416,plain,(
% 1.24/0.53    $false),
% 1.24/0.53    inference(subsumption_resolution,[],[f415,f413])).
% 1.24/0.53  fof(f413,plain,(
% 1.24/0.53    k1_xboole_0 != k1_tarski(sK0)),
% 1.24/0.53    inference(backward_demodulation,[],[f402,f410])).
% 1.24/0.53  fof(f410,plain,(
% 1.24/0.53    k1_xboole_0 = sK2),
% 1.24/0.53    inference(subsumption_resolution,[],[f398,f402])).
% 1.24/0.53  fof(f398,plain,(
% 1.24/0.53    k1_xboole_0 = sK2 | sK2 = k1_tarski(sK0)),
% 1.24/0.53    inference(resolution,[],[f396,f53])).
% 1.24/0.53  fof(f53,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.24/0.53    inference(cnf_transformation,[],[f34])).
% 1.24/0.53  fof(f34,plain,(
% 1.24/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.24/0.53    inference(flattening,[],[f33])).
% 1.24/0.53  fof(f33,plain,(
% 1.24/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.24/0.53    inference(nnf_transformation,[],[f19])).
% 1.24/0.53  fof(f19,axiom,(
% 1.24/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.24/0.53  fof(f396,plain,(
% 1.24/0.53    r1_tarski(sK2,k1_tarski(sK0))),
% 1.24/0.53    inference(superposition,[],[f370,f36])).
% 1.24/0.53  fof(f36,plain,(
% 1.24/0.53    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.24/0.53    inference(cnf_transformation,[],[f28])).
% 1.24/0.53  fof(f28,plain,(
% 1.24/0.53    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.24/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27])).
% 1.24/0.53  fof(f27,plain,(
% 1.24/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.24/0.53    introduced(choice_axiom,[])).
% 1.24/0.53  fof(f24,plain,(
% 1.24/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.24/0.53    inference(ennf_transformation,[],[f22])).
% 1.24/0.53  fof(f22,negated_conjecture,(
% 1.24/0.53    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.24/0.53    inference(negated_conjecture,[],[f21])).
% 1.24/0.53  fof(f21,conjecture,(
% 1.24/0.53    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.24/0.53  fof(f370,plain,(
% 1.24/0.53    ( ! [X4,X5] : (r1_tarski(X4,k2_xboole_0(X5,X4))) )),
% 1.24/0.53    inference(superposition,[],[f44,f332])).
% 1.24/0.53  fof(f332,plain,(
% 1.24/0.53    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 1.24/0.53    inference(superposition,[],[f321,f225])).
% 1.24/0.53  fof(f225,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.24/0.53    inference(forward_demodulation,[],[f210,f113])).
% 1.24/0.53  fof(f113,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 1.24/0.53    inference(superposition,[],[f49,f45])).
% 1.24/0.53  fof(f45,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f1])).
% 1.24/0.53  fof(f1,axiom,(
% 1.24/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.24/0.53  fof(f49,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f6])).
% 1.24/0.53  fof(f6,axiom,(
% 1.24/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.24/0.53  fof(f210,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 1.24/0.53    inference(superposition,[],[f59,f50])).
% 1.24/0.53  fof(f50,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f11])).
% 1.24/0.53  fof(f11,axiom,(
% 1.24/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.24/0.53  fof(f59,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f10])).
% 1.24/0.53  fof(f10,axiom,(
% 1.24/0.53    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.24/0.53  fof(f321,plain,(
% 1.24/0.53    ( ! [X4,X3] : (k5_xboole_0(X3,k4_xboole_0(X4,X3)) = k2_xboole_0(X4,X3)) )),
% 1.24/0.53    inference(forward_demodulation,[],[f298,f49])).
% 1.24/0.53  fof(f298,plain,(
% 1.24/0.53    ( ! [X4,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))) = k2_xboole_0(X4,X3)) )),
% 1.24/0.53    inference(superposition,[],[f154,f59])).
% 1.24/0.53  fof(f154,plain,(
% 1.24/0.53    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X2,X1),k3_xboole_0(X1,X2))) )),
% 1.24/0.53    inference(superposition,[],[f50,f46])).
% 1.24/0.53  fof(f46,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f2])).
% 1.24/0.53  fof(f2,axiom,(
% 1.24/0.53    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.24/0.53  fof(f44,plain,(
% 1.24/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f9])).
% 1.24/0.53  fof(f9,axiom,(
% 1.24/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.24/0.53  fof(f402,plain,(
% 1.24/0.53    sK2 != k1_tarski(sK0)),
% 1.24/0.53    inference(subsumption_resolution,[],[f38,f401])).
% 1.24/0.53  fof(f401,plain,(
% 1.24/0.53    k1_xboole_0 = sK1),
% 1.24/0.53    inference(global_subsumption,[],[f37,f179,f196,f398])).
% 1.24/0.53  fof(f196,plain,(
% 1.24/0.53    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.24/0.53    inference(trivial_inequality_removal,[],[f189])).
% 1.24/0.53  fof(f189,plain,(
% 1.24/0.53    sK1 != sK1 | k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.24/0.53    inference(superposition,[],[f39,f179])).
% 1.24/0.53  fof(f39,plain,(
% 1.24/0.53    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.24/0.53    inference(cnf_transformation,[],[f28])).
% 1.24/0.53  fof(f179,plain,(
% 1.24/0.53    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 1.24/0.53    inference(resolution,[],[f53,f68])).
% 1.24/0.53  fof(f68,plain,(
% 1.24/0.53    r1_tarski(sK1,k1_tarski(sK0))),
% 1.24/0.53    inference(superposition,[],[f44,f36])).
% 1.24/0.53  fof(f37,plain,(
% 1.24/0.53    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.24/0.53    inference(cnf_transformation,[],[f28])).
% 1.24/0.53  fof(f38,plain,(
% 1.24/0.53    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.24/0.53    inference(cnf_transformation,[],[f28])).
% 1.24/0.53  fof(f415,plain,(
% 1.24/0.53    k1_xboole_0 = k1_tarski(sK0)),
% 1.24/0.53    inference(forward_demodulation,[],[f414,f410])).
% 1.24/0.53  fof(f414,plain,(
% 1.24/0.53    sK2 = k1_tarski(sK0)),
% 1.24/0.53    inference(forward_demodulation,[],[f403,f171])).
% 1.24/0.53  fof(f171,plain,(
% 1.24/0.53    ( ! [X9] : (k2_xboole_0(k1_xboole_0,X9) = X9) )),
% 1.24/0.53    inference(forward_demodulation,[],[f170,f119])).
% 1.24/0.53  fof(f119,plain,(
% 1.24/0.53    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = X4) )),
% 1.24/0.53    inference(forward_demodulation,[],[f115,f41])).
% 1.24/0.53  fof(f41,plain,(
% 1.24/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.24/0.53    inference(cnf_transformation,[],[f7])).
% 1.24/0.53  fof(f7,axiom,(
% 1.24/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.24/0.53  fof(f115,plain,(
% 1.24/0.53    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k1_xboole_0)) )),
% 1.24/0.53    inference(superposition,[],[f49,f81])).
% 1.24/0.53  fof(f81,plain,(
% 1.24/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.24/0.53    inference(resolution,[],[f80,f43])).
% 1.24/0.53  fof(f43,plain,(
% 1.24/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.24/0.53    inference(cnf_transformation,[],[f30])).
% 1.24/0.53  fof(f30,plain,(
% 1.24/0.53    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.24/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f29])).
% 1.24/0.53  fof(f29,plain,(
% 1.24/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.24/0.53    introduced(choice_axiom,[])).
% 1.24/0.53  fof(f25,plain,(
% 1.24/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.24/0.53    inference(ennf_transformation,[],[f4])).
% 1.24/0.53  fof(f4,axiom,(
% 1.24/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.24/0.53  fof(f80,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 1.24/0.53    inference(resolution,[],[f52,f40])).
% 1.24/0.53  fof(f40,plain,(
% 1.24/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f8])).
% 1.24/0.53  fof(f8,axiom,(
% 1.24/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.24/0.53  fof(f52,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f32])).
% 1.24/0.53  fof(f32,plain,(
% 1.24/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.24/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f31])).
% 1.24/0.53  fof(f31,plain,(
% 1.24/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.24/0.53    introduced(choice_axiom,[])).
% 1.24/0.53  fof(f26,plain,(
% 1.24/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.24/0.53    inference(ennf_transformation,[],[f23])).
% 1.24/0.53  fof(f23,plain,(
% 1.24/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.24/0.53    inference(rectify,[],[f3])).
% 1.24/0.53  fof(f3,axiom,(
% 1.24/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.24/0.53  fof(f170,plain,(
% 1.24/0.53    ( ! [X9] : (k2_xboole_0(k1_xboole_0,X9) = k4_xboole_0(X9,k1_xboole_0)) )),
% 1.24/0.53    inference(forward_demodulation,[],[f158,f113])).
% 1.24/0.53  fof(f158,plain,(
% 1.24/0.53    ( ! [X9] : (k2_xboole_0(k1_xboole_0,X9) = k5_xboole_0(X9,k3_xboole_0(k1_xboole_0,X9))) )),
% 1.24/0.53    inference(superposition,[],[f50,f69])).
% 1.24/0.53  fof(f69,plain,(
% 1.24/0.53    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.24/0.53    inference(superposition,[],[f46,f41])).
% 1.24/0.53  fof(f403,plain,(
% 1.24/0.53    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)),
% 1.24/0.53    inference(backward_demodulation,[],[f36,f401])).
% 1.24/0.53  % SZS output end Proof for theBenchmark
% 1.24/0.53  % (22365)------------------------------
% 1.24/0.53  % (22365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (22365)Termination reason: Refutation
% 1.24/0.53  
% 1.24/0.53  % (22365)Memory used [KB]: 6524
% 1.24/0.53  % (22365)Time elapsed: 0.099 s
% 1.24/0.53  % (22365)------------------------------
% 1.24/0.53  % (22365)------------------------------
% 1.24/0.53  % (22357)Success in time 0.168 s
%------------------------------------------------------------------------------
