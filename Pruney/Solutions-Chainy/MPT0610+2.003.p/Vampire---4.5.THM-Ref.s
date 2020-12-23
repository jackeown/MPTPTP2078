%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:30 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   47 (  80 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :   14
%              Number of atoms          :  110 ( 255 expanded)
%              Number of equality atoms :   40 (  45 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f867,plain,(
    $false ),
    inference(subsumption_resolution,[],[f866,f91])).

fof(f91,plain,(
    k1_xboole_0 != k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f53,f38])).

fof(f38,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK0,X1)
          & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ~ r1_xboole_0(sK0,X1)
        & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_xboole_0(sK0,sK1)
      & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f866,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f865,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f865,plain,(
    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f836,f58])).

fof(f58,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f836,plain,(
    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k3_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f419,f202])).

fof(f202,plain,(
    k1_xboole_0 = k1_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f201,f40])).

fof(f201,plain,(
    k1_relat_1(k3_xboole_0(sK0,sK1)) = k3_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) ),
    inference(resolution,[],[f200,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f200,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f197,f88])).

fof(f88,plain,(
    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f52,f37])).

fof(f37,plain,(
    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f197,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(resolution,[],[f187,f36])).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f187,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | r1_tarski(k1_relat_1(k3_xboole_0(sK0,X7)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X7))) ) ),
    inference(resolution,[],[f44,f35])).

fof(f35,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

fof(f419,plain,(
    ! [X7] : k3_xboole_0(sK0,X7) = k3_xboole_0(k3_xboole_0(sK0,X7),k2_zfmisc_1(k1_relat_1(k3_xboole_0(sK0,X7)),k2_relat_1(k3_xboole_0(sK0,X7)))) ),
    inference(resolution,[],[f156,f35])).

fof(f156,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),k2_zfmisc_1(k1_relat_1(k3_xboole_0(X2,X3)),k2_relat_1(k3_xboole_0(X2,X3)))) ) ),
    inference(resolution,[],[f41,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n015.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 14:16:08 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.18/0.45  % (29907)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.18/0.46  % (29915)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.18/0.51  % (29907)Refutation found. Thanks to Tanya!
% 0.18/0.51  % SZS status Theorem for theBenchmark
% 0.18/0.51  % SZS output start Proof for theBenchmark
% 0.18/0.51  fof(f867,plain,(
% 0.18/0.51    $false),
% 0.18/0.51    inference(subsumption_resolution,[],[f866,f91])).
% 0.18/0.51  fof(f91,plain,(
% 0.18/0.51    k1_xboole_0 != k3_xboole_0(sK0,sK1)),
% 0.18/0.51    inference(resolution,[],[f53,f38])).
% 0.18/0.51  fof(f38,plain,(
% 0.18/0.51    ~r1_xboole_0(sK0,sK1)),
% 0.18/0.51    inference(cnf_transformation,[],[f28])).
% 0.18/0.51  fof(f28,plain,(
% 0.18/0.51    (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.18/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f27,f26])).
% 0.18/0.51  fof(f26,plain,(
% 0.18/0.51    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.18/0.51    introduced(choice_axiom,[])).
% 0.18/0.51  fof(f27,plain,(
% 0.18/0.51    ? [X1] : (~r1_xboole_0(sK0,X1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_xboole_0(sK0,sK1) & r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.18/0.51    introduced(choice_axiom,[])).
% 0.18/0.51  fof(f18,plain,(
% 0.18/0.51    ? [X0] : (? [X1] : (~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.18/0.51    inference(flattening,[],[f17])).
% 0.18/0.51  fof(f17,plain,(
% 0.18/0.51    ? [X0] : (? [X1] : ((~r1_xboole_0(X0,X1) & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.18/0.51    inference(ennf_transformation,[],[f15])).
% 0.18/0.51  fof(f15,negated_conjecture,(
% 0.18/0.51    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.18/0.51    inference(negated_conjecture,[],[f14])).
% 0.18/0.51  fof(f14,conjecture,(
% 0.18/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) => r1_xboole_0(X0,X1))))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).
% 0.18/0.51  fof(f53,plain,(
% 0.18/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.18/0.51    inference(cnf_transformation,[],[f32])).
% 0.18/0.51  fof(f32,plain,(
% 0.18/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.18/0.51    inference(nnf_transformation,[],[f2])).
% 0.18/0.51  fof(f2,axiom,(
% 0.18/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.18/0.51  fof(f866,plain,(
% 0.18/0.51    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.18/0.51    inference(forward_demodulation,[],[f865,f40])).
% 0.18/0.51  fof(f40,plain,(
% 0.18/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.18/0.51    inference(cnf_transformation,[],[f6])).
% 0.18/0.51  fof(f6,axiom,(
% 0.18/0.51    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.18/0.51  fof(f865,plain,(
% 0.18/0.51    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.18/0.51    inference(forward_demodulation,[],[f836,f58])).
% 0.18/0.51  fof(f58,plain,(
% 0.18/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.18/0.51    inference(equality_resolution,[],[f55])).
% 0.18/0.51  fof(f55,plain,(
% 0.18/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.18/0.51    inference(cnf_transformation,[],[f34])).
% 0.18/0.51  fof(f34,plain,(
% 0.18/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.18/0.51    inference(flattening,[],[f33])).
% 0.18/0.51  fof(f33,plain,(
% 0.18/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.18/0.51    inference(nnf_transformation,[],[f8])).
% 0.18/0.51  fof(f8,axiom,(
% 0.18/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.18/0.51  fof(f836,plain,(
% 0.18/0.51    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k3_xboole_0(sK0,sK1))))),
% 0.18/0.51    inference(superposition,[],[f419,f202])).
% 0.18/0.51  fof(f202,plain,(
% 0.18/0.51    k1_xboole_0 = k1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.18/0.51    inference(forward_demodulation,[],[f201,f40])).
% 0.18/0.51  fof(f201,plain,(
% 0.18/0.51    k1_relat_1(k3_xboole_0(sK0,sK1)) = k3_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)),
% 0.18/0.51    inference(resolution,[],[f200,f50])).
% 0.18/0.51  fof(f50,plain,(
% 0.18/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.18/0.51    inference(cnf_transformation,[],[f24])).
% 0.18/0.51  fof(f24,plain,(
% 0.18/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.18/0.51    inference(ennf_transformation,[],[f5])).
% 0.18/0.51  fof(f5,axiom,(
% 0.18/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.18/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.18/0.53  fof(f200,plain,(
% 0.18/0.53    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_xboole_0)),
% 0.18/0.53    inference(forward_demodulation,[],[f197,f88])).
% 0.18/0.53  fof(f88,plain,(
% 0.18/0.53    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.18/0.53    inference(resolution,[],[f52,f37])).
% 0.18/0.53  fof(f37,plain,(
% 0.18/0.53    r1_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.18/0.53    inference(cnf_transformation,[],[f28])).
% 0.18/0.53  fof(f52,plain,(
% 0.18/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.18/0.53    inference(cnf_transformation,[],[f32])).
% 0.18/0.53  fof(f197,plain,(
% 0.18/0.53    r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 0.18/0.53    inference(resolution,[],[f187,f36])).
% 0.18/0.53  fof(f36,plain,(
% 0.18/0.53    v1_relat_1(sK1)),
% 0.18/0.53    inference(cnf_transformation,[],[f28])).
% 0.18/0.53  fof(f187,plain,(
% 0.18/0.53    ( ! [X7] : (~v1_relat_1(X7) | r1_tarski(k1_relat_1(k3_xboole_0(sK0,X7)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X7)))) )),
% 0.18/0.53    inference(resolution,[],[f44,f35])).
% 0.18/0.53  fof(f35,plain,(
% 0.18/0.53    v1_relat_1(sK0)),
% 0.18/0.53    inference(cnf_transformation,[],[f28])).
% 0.18/0.53  fof(f44,plain,(
% 0.18/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))) )),
% 0.18/0.53    inference(cnf_transformation,[],[f21])).
% 0.18/0.53  fof(f21,plain,(
% 0.18/0.53    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.18/0.53    inference(ennf_transformation,[],[f11])).
% 0.18/0.53  fof(f11,axiom,(
% 0.18/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).
% 0.18/0.53  fof(f419,plain,(
% 0.18/0.53    ( ! [X7] : (k3_xboole_0(sK0,X7) = k3_xboole_0(k3_xboole_0(sK0,X7),k2_zfmisc_1(k1_relat_1(k3_xboole_0(sK0,X7)),k2_relat_1(k3_xboole_0(sK0,X7))))) )),
% 0.18/0.53    inference(resolution,[],[f156,f35])).
% 0.18/0.53  fof(f156,plain,(
% 0.18/0.53    ( ! [X2,X3] : (~v1_relat_1(X2) | k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),k2_zfmisc_1(k1_relat_1(k3_xboole_0(X2,X3)),k2_relat_1(k3_xboole_0(X2,X3))))) )),
% 0.18/0.53    inference(resolution,[],[f41,f49])).
% 0.18/0.53  fof(f49,plain,(
% 0.18/0.53    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.18/0.53    inference(cnf_transformation,[],[f23])).
% 0.18/0.53  fof(f23,plain,(
% 0.18/0.53    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.18/0.53    inference(ennf_transformation,[],[f10])).
% 0.18/0.53  fof(f10,axiom,(
% 0.18/0.53    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.18/0.53  fof(f41,plain,(
% 0.18/0.53    ( ! [X0] : (~v1_relat_1(X0) | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0) )),
% 0.18/0.53    inference(cnf_transformation,[],[f19])).
% 0.18/0.53  fof(f19,plain,(
% 0.18/0.53    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.18/0.53    inference(ennf_transformation,[],[f12])).
% 0.18/0.53  fof(f12,axiom,(
% 0.18/0.53    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.18/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 0.18/0.53  % SZS output end Proof for theBenchmark
% 0.18/0.53  % (29907)------------------------------
% 0.18/0.53  % (29907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.53  % (29907)Termination reason: Refutation
% 0.18/0.53  
% 0.18/0.53  % (29907)Memory used [KB]: 6908
% 0.18/0.53  % (29907)Time elapsed: 0.119 s
% 0.18/0.53  % (29907)------------------------------
% 0.18/0.53  % (29907)------------------------------
% 0.18/0.53  % (29899)Success in time 0.192 s
%------------------------------------------------------------------------------
