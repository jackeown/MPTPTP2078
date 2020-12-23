%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 (  82 expanded)
%              Number of leaves         :    5 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 259 expanded)
%              Number of equality atoms :    2 (  16 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39,plain,(
    $false ),
    inference(subsumption_resolution,[],[f38,f37])).

fof(f37,plain,(
    ~ r1_xboole_0(sK0,sK4) ),
    inference(resolution,[],[f33,f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f33,plain,(
    ~ r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f30,f11])).

fof(f11,plain,(
    ~ r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ( r1_xboole_0(sK3,sK7)
      | r1_xboole_0(sK2,sK6)
      | r1_xboole_0(sK1,sK5)
      | r1_xboole_0(sK0,sK4) )
    & ~ r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( r1_xboole_0(X3,X7)
          | r1_xboole_0(X2,X6)
          | r1_xboole_0(X1,X5)
          | r1_xboole_0(X0,X4) )
        & ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
   => ( ( r1_xboole_0(sK3,sK7)
        | r1_xboole_0(sK2,sK6)
        | r1_xboole_0(sK1,sK5)
        | r1_xboole_0(sK0,sK4) )
      & ~ r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( r1_xboole_0(X3,X7)
        | r1_xboole_0(X2,X6)
        | r1_xboole_0(X1,X5)
        | r1_xboole_0(X0,X4) )
      & ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
       => ( ~ r1_xboole_0(X3,X7)
          & ~ r1_xboole_0(X2,X6)
          & ~ r1_xboole_0(X1,X5)
          & ~ r1_xboole_0(X0,X4) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ~ r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
     => ( ~ r1_xboole_0(X3,X7)
        & ~ r1_xboole_0(X2,X6)
        & ~ r1_xboole_0(X1,X5)
        & ~ r1_xboole_0(X0,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_mcart_1)).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_xboole_0(k4_zfmisc_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3))
      | ~ r1_xboole_0(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f19,f13])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_mcart_1)).

fof(f19,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k3_zfmisc_1(X4,X5,X6))
      | ~ r1_xboole_0(k2_zfmisc_1(X0,X1),X4) ) ),
    inference(superposition,[],[f16,f13])).

fof(f16,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
      | ~ r1_xboole_0(X0,X3) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ~ r1_xboole_0(X2,X5)
        & ~ r1_xboole_0(X1,X4)
        & ~ r1_xboole_0(X0,X3) )
      | r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(ennf_transformation,[],[f2])).

% (23932)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
     => ( ~ r1_xboole_0(X2,X5)
        & ~ r1_xboole_0(X1,X4)
        & ~ r1_xboole_0(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_mcart_1)).

fof(f38,plain,(
    r1_xboole_0(sK0,sK4) ),
    inference(resolution,[],[f35,f36])).

fof(f36,plain,(
    ~ r1_xboole_0(sK1,sK5) ),
    inference(resolution,[],[f33,f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,
    ( r1_xboole_0(sK1,sK5)
    | r1_xboole_0(sK0,sK4) ),
    inference(subsumption_resolution,[],[f34,f29])).

fof(f29,plain,(
    ~ r1_xboole_0(sK2,sK6) ),
    inference(resolution,[],[f25,f11])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_xboole_0(k4_zfmisc_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3))
      | ~ r1_xboole_0(X6,X2) ) ),
    inference(superposition,[],[f21,f13])).

fof(f21,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k3_zfmisc_1(X4,X5,X6))
      | ~ r1_xboole_0(X2,X5) ) ),
    inference(superposition,[],[f17,f13])).

fof(f17,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
      | ~ r1_xboole_0(X1,X4) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,
    ( r1_xboole_0(sK2,sK6)
    | r1_xboole_0(sK1,sK5)
    | r1_xboole_0(sK0,sK4) ),
    inference(resolution,[],[f32,f12])).

fof(f12,plain,
    ( r1_xboole_0(sK3,sK7)
    | r1_xboole_0(sK2,sK6)
    | r1_xboole_0(sK1,sK5)
    | r1_xboole_0(sK0,sK4) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ~ r1_xboole_0(sK3,sK7) ),
    inference(resolution,[],[f27,f11])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r1_xboole_0(k4_zfmisc_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3))
      | ~ r1_xboole_0(X7,X3) ) ),
    inference(superposition,[],[f23,f13])).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k3_zfmisc_1(X4,X5,X6))
      | ~ r1_xboole_0(X3,X6) ) ),
    inference(superposition,[],[f18,f13])).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
      | ~ r1_xboole_0(X2,X5) ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:11:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (23921)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (23919)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (23929)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (23927)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (23927)Refutation not found, incomplete strategy% (23927)------------------------------
% 0.22/0.48  % (23927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (23927)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (23927)Memory used [KB]: 10618
% 0.22/0.48  % (23927)Time elapsed: 0.062 s
% 0.22/0.48  % (23927)------------------------------
% 0.22/0.48  % (23927)------------------------------
% 0.22/0.48  % (23922)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (23930)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (23919)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f38,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ~r1_xboole_0(sK0,sK4)),
% 0.22/0.48    inference(resolution,[],[f33,f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ~r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK4,sK5))),
% 0.22/0.48    inference(resolution,[],[f30,f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ~r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    (r1_xboole_0(sK3,sK7) | r1_xboole_0(sK2,sK6) | r1_xboole_0(sK1,sK5) | r1_xboole_0(sK0,sK4)) & ~r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f6,f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((r1_xboole_0(X3,X7) | r1_xboole_0(X2,X6) | r1_xboole_0(X1,X5) | r1_xboole_0(X0,X4)) & ~r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))) => ((r1_xboole_0(sK3,sK7) | r1_xboole_0(sK2,sK6) | r1_xboole_0(sK1,sK5) | r1_xboole_0(sK0,sK4)) & ~r1_xboole_0(k4_zfmisc_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f6,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((r1_xboole_0(X3,X7) | r1_xboole_0(X2,X6) | r1_xboole_0(X1,X5) | r1_xboole_0(X0,X4)) & ~r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (~r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) => (~r1_xboole_0(X3,X7) & ~r1_xboole_0(X2,X6) & ~r1_xboole_0(X1,X5) & ~r1_xboole_0(X0,X4)))),
% 0.22/0.48    inference(negated_conjecture,[],[f4])).
% 0.22/0.48  fof(f4,conjecture,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (~r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) => (~r1_xboole_0(X3,X7) & ~r1_xboole_0(X2,X6) & ~r1_xboole_0(X1,X5) & ~r1_xboole_0(X0,X4)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_mcart_1)).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_xboole_0(k4_zfmisc_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) | ~r1_xboole_0(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X0,X1))) )),
% 0.22/0.48    inference(superposition,[],[f19,f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_mcart_1)).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k3_zfmisc_1(X4,X5,X6)) | ~r1_xboole_0(k2_zfmisc_1(X0,X1),X4)) )),
% 0.22/0.48    inference(superposition,[],[f16,f13])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) | ~r1_xboole_0(X0,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5] : ((~r1_xboole_0(X2,X5) & ~r1_xboole_0(X1,X4) & ~r1_xboole_0(X0,X3)) | r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  % (23932)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5] : (~r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) => (~r1_xboole_0(X2,X5) & ~r1_xboole_0(X1,X4) & ~r1_xboole_0(X0,X3)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_mcart_1)).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    r1_xboole_0(sK0,sK4)),
% 0.22/0.48    inference(resolution,[],[f35,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ~r1_xboole_0(sK1,sK5)),
% 0.22/0.48    inference(resolution,[],[f33,f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X2,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    r1_xboole_0(sK1,sK5) | r1_xboole_0(sK0,sK4)),
% 0.22/0.48    inference(subsumption_resolution,[],[f34,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ~r1_xboole_0(sK2,sK6)),
% 0.22/0.48    inference(resolution,[],[f25,f11])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_xboole_0(k4_zfmisc_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) | ~r1_xboole_0(X6,X2)) )),
% 0.22/0.48    inference(superposition,[],[f21,f13])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k3_zfmisc_1(X4,X5,X6)) | ~r1_xboole_0(X2,X5)) )),
% 0.22/0.48    inference(superposition,[],[f17,f13])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) | ~r1_xboole_0(X1,X4)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    r1_xboole_0(sK2,sK6) | r1_xboole_0(sK1,sK5) | r1_xboole_0(sK0,sK4)),
% 0.22/0.48    inference(resolution,[],[f32,f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    r1_xboole_0(sK3,sK7) | r1_xboole_0(sK2,sK6) | r1_xboole_0(sK1,sK5) | r1_xboole_0(sK0,sK4)),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ~r1_xboole_0(sK3,sK7)),
% 0.22/0.48    inference(resolution,[],[f27,f11])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_xboole_0(k4_zfmisc_1(X4,X5,X6,X7),k4_zfmisc_1(X0,X1,X2,X3)) | ~r1_xboole_0(X7,X3)) )),
% 0.22/0.48    inference(superposition,[],[f23,f13])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_xboole_0(k4_zfmisc_1(X0,X1,X2,X3),k3_zfmisc_1(X4,X5,X6)) | ~r1_xboole_0(X3,X6)) )),
% 0.22/0.48    inference(superposition,[],[f18,f13])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) | ~r1_xboole_0(X2,X5)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (23919)------------------------------
% 0.22/0.48  % (23919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (23919)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (23919)Memory used [KB]: 1663
% 0.22/0.48  % (23919)Time elapsed: 0.063 s
% 0.22/0.48  % (23919)------------------------------
% 0.22/0.48  % (23919)------------------------------
% 0.22/0.48  % (23915)Success in time 0.119 s
%------------------------------------------------------------------------------
