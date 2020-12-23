%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 121 expanded)
%              Number of leaves         :    5 (  27 expanded)
%              Depth                    :   20
%              Number of atoms          :  117 ( 428 expanded)
%              Number of equality atoms :   61 ( 233 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(subsumption_resolution,[],[f71,f31])).

fof(f31,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f71,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(resolution,[],[f68,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f68,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f67,f31])).

fof(f67,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) ),
    inference(resolution,[],[f61,f24])).

fof(f61,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(resolution,[],[f60,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f60,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(forward_demodulation,[],[f59,f57])).

fof(f57,plain,(
    sK1 = sK3 ),
    inference(subsumption_resolution,[],[f56,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,
    ( sK1 = sK3
    | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK3)) ),
    inference(resolution,[],[f38,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,
    ( r2_hidden(sK1,k1_tarski(sK3))
    | sK1 = sK3 ),
    inference(resolution,[],[f19,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f19,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))
    | sK1 = sK3 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( sK1 != sK3
      | sK0 != sK2
      | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) )
    & ( ( sK1 = sK3
        & sK0 = sK2 )
      | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
        & ( ( X1 = X3
            & X0 = X2 )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) )
   => ( ( sK1 != sK3
        | sK0 != sK2
        | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) )
      & ( ( sK1 = sK3
          & sK0 = sK2 )
        | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
      & ( ( X1 = X3
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) )
      & ( ( X1 = X3
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <~> ( X1 = X3
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      <=> ( X1 = X3
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f59,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK3))) ),
    inference(trivial_inequality_removal,[],[f58])).

fof(f58,plain,
    ( sK1 != sK1
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK3))) ),
    inference(backward_demodulation,[],[f53,f57])).

fof(f53,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK3)))
    | sK1 != sK3 ),
    inference(forward_demodulation,[],[f52,f45])).

fof(f45,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f44,f26])).

fof(f44,plain,
    ( sK0 = sK2
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK2)) ),
    inference(resolution,[],[f32,f23])).

fof(f32,plain,
    ( r2_hidden(sK0,k1_tarski(sK2))
    | sK0 = sK2 ),
    inference(resolution,[],[f18,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))
    | sK0 = sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f52,plain,
    ( sK1 != sK3
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(trivial_inequality_removal,[],[f47])).

fof(f47,plain,
    ( sK0 != sK0
    | sK1 != sK3
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(backward_demodulation,[],[f20,f45])).

fof(f20,plain,
    ( sK1 != sK3
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:37:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.55  % (27484)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (27476)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (27484)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(subsumption_resolution,[],[f71,f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.22/0.56    inference(equality_resolution,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.22/0.56    inference(nnf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.22/0.56    inference(resolution,[],[f68,f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.22/0.56    inference(nnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    ~r2_hidden(sK0,k1_tarski(sK0))),
% 0.22/0.56    inference(subsumption_resolution,[],[f67,f31])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    ~r2_hidden(sK0,k1_tarski(sK0)) | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1))),
% 0.22/0.56    inference(resolution,[],[f61,f24])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ~r2_hidden(sK1,k1_tarski(sK1)) | ~r2_hidden(sK0,k1_tarski(sK0))),
% 0.22/0.56    inference(resolution,[],[f60,f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.56    inference(flattening,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.56    inference(nnf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.22/0.56    inference(forward_demodulation,[],[f59,f57])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    sK1 = sK3),
% 0.22/0.56    inference(subsumption_resolution,[],[f56,f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    sK1 = sK3 | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_tarski(sK3))),
% 0.22/0.56    inference(resolution,[],[f38,f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    r2_hidden(sK1,k1_tarski(sK3)) | sK1 = sK3),
% 0.22/0.56    inference(resolution,[],[f19,f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) | sK1 = sK3),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    (sK1 != sK3 | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))) & ((sK1 = sK3 & sK0 = sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f12])).
% 0.22/0.56  fof(f12,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) & ((X1 = X3 & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))))) => ((sK1 != sK3 | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))) & ((sK1 = sK3 & sK0 = sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f11,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) & ((X1 = X3 & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 0.22/0.56    inference(flattening,[],[f10])).
% 0.22/0.56  fof(f10,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) & ((X1 = X3 & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 0.22/0.56    inference(nnf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <~> (X1 = X3 & X0 = X2))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 0.22/0.56    inference(negated_conjecture,[],[f7])).
% 0.22/0.56  fof(f7,conjecture,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK3)))),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    sK1 != sK1 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK3)))),
% 0.22/0.56    inference(backward_demodulation,[],[f53,f57])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),k1_tarski(sK3))) | sK1 != sK3),
% 0.22/0.56    inference(forward_demodulation,[],[f52,f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    sK0 = sK2),
% 0.22/0.56    inference(subsumption_resolution,[],[f44,f26])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    sK0 = sK2 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK2))),
% 0.22/0.56    inference(resolution,[],[f32,f23])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    r2_hidden(sK0,k1_tarski(sK2)) | sK0 = sK2),
% 0.22/0.56    inference(resolution,[],[f18,f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3))) | sK0 = sK2),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    sK1 != sK3 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f47])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    sK0 != sK0 | sK1 != sK3 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))),
% 0.22/0.56    inference(backward_demodulation,[],[f20,f45])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    sK1 != sK3 | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),k1_tarski(sK3)))),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (27484)------------------------------
% 0.22/0.56  % (27484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (27484)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (27484)Memory used [KB]: 1791
% 0.22/0.56  % (27484)Time elapsed: 0.076 s
% 0.22/0.56  % (27484)------------------------------
% 0.22/0.56  % (27484)------------------------------
% 0.22/0.56  % (27460)Success in time 0.198 s
%------------------------------------------------------------------------------
