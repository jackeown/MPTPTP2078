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
% DateTime   : Thu Dec  3 12:41:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 643 expanded)
%              Number of leaves         :    4 ( 124 expanded)
%              Depth                    :   22
%              Number of atoms          :  204 (3918 expanded)
%              Number of equality atoms :  165 (3466 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f244,plain,(
    $false ),
    inference(subsumption_resolution,[],[f243,f66])).

fof(f66,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f243,plain,(
    ~ r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2)) ),
    inference(forward_demodulation,[],[f235,f185])).

fof(f185,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f172,f158])).

fof(f158,plain,
    ( sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f144,f121])).

fof(f121,plain,
    ( sK0 = k1_tarski(sK2)
    | k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f115,f119])).

fof(f119,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK2) ),
    inference(trivial_inequality_removal,[],[f110])).

fof(f110,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 != sK0
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK2) ),
    inference(superposition,[],[f84,f100])).

fof(f100,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK2) ),
    inference(subsumption_resolution,[],[f99,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f99,plain,
    ( r1_tarski(sK0,k2_tarski(sK1,sK2))
    | sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | sK0 = k2_tarski(sK1,sK2) ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k2_tarski(sK1,sK2))
    | sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | sK0 = k2_tarski(sK1,sK2) ),
    inference(superposition,[],[f49,f33])).

fof(f33,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | sK0 = k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ( sK0 != k2_tarski(sK1,sK2)
        & sK0 != k1_tarski(sK2)
        & sK0 != k1_tarski(sK1)
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) )
    & ( sK0 = k2_tarski(sK1,sK2)
      | sK0 = k1_tarski(sK2)
      | sK0 = k1_tarski(sK1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ( ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
        & ( k2_tarski(X1,X2) = X0
          | k1_tarski(X2) = X0
          | k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) )
   => ( ( ( sK0 != k2_tarski(sK1,sK2)
          & sK0 != k1_tarski(sK2)
          & sK0 != k1_tarski(sK1)
          & k1_xboole_0 != sK0 )
        | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) )
      & ( sK0 = k2_tarski(sK1,sK2)
        | sK0 = k1_tarski(sK2)
        | sK0 = k1_tarski(sK1)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f84,plain,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | sK0 != k2_tarski(sK1,sK2) ),
    inference(trivial_inequality_removal,[],[f83])).

fof(f83,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 != k2_tarski(sK1,sK2)
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(superposition,[],[f37,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f37,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | sK0 != k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f115,plain,
    ( r1_tarski(sK0,sK0)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK2) ),
    inference(superposition,[],[f63,f100])).

fof(f63,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f144,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | sK0 != k1_tarski(sK2) ),
    inference(resolution,[],[f127,f79])).

fof(f79,plain,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | sK0 != k1_tarski(sK2) ),
    inference(trivial_inequality_removal,[],[f78])).

fof(f78,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 != k1_tarski(sK2)
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(superposition,[],[f36,f50])).

fof(f36,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | sK0 != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f127,plain,(
    ! [X5] :
      ( r1_tarski(sK0,k2_tarski(X5,sK2))
      | k1_xboole_0 = sK0
      | sK0 = k1_tarski(sK1) ) ),
    inference(superposition,[],[f64,f121])).

fof(f64,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f172,plain,
    ( k1_xboole_0 = sK0
    | sK0 != k1_tarski(sK1) ),
    inference(resolution,[],[f163,f72])).

fof(f72,plain,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | sK0 != k1_tarski(sK1) ),
    inference(trivial_inequality_removal,[],[f71])).

fof(f71,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 != k1_tarski(sK1)
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(superposition,[],[f35,f50])).

fof(f35,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f163,plain,(
    ! [X4] :
      ( r1_tarski(sK0,k2_tarski(sK1,X4))
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f65,f158])).

fof(f65,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f235,plain,(
    ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f192])).

fof(f192,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(backward_demodulation,[],[f69,f185])).

fof(f69,plain,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | k1_xboole_0 != sK0 ),
    inference(trivial_inequality_removal,[],[f68])).

fof(f68,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(superposition,[],[f34,f50])).

fof(f34,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:41:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (17662)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (17654)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (17654)Refutation not found, incomplete strategy% (17654)------------------------------
% 0.21/0.52  % (17654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (17654)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (17654)Memory used [KB]: 6140
% 0.21/0.52  % (17654)Time elapsed: 0.003 s
% 0.21/0.52  % (17654)------------------------------
% 0.21/0.52  % (17654)------------------------------
% 0.21/0.52  % (17646)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (17641)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (17662)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f243,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k2_tarski(X1,X2))) )),
% 0.21/0.52    inference(equality_resolution,[],[f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_xboole_0 != X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.21/0.52    inference(flattening,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.21/0.52    inference(nnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.21/0.52  fof(f243,plain,(
% 0.21/0.52    ~r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2))),
% 0.21/0.52    inference(forward_demodulation,[],[f235,f185])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f172,f158])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f144,f121])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    sK0 = k1_tarski(sK2) | k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f115,f119])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    ~r1_tarski(sK0,sK0) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | sK0 = k1_tarski(sK2)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f110])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ~r1_tarski(sK0,sK0) | sK0 != sK0 | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | sK0 = k1_tarski(sK2)),
% 0.21/0.52    inference(superposition,[],[f84,f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | sK0 = k1_tarski(sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f99,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    r1_tarski(sK0,k2_tarski(sK1,sK2)) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | sK0 = k2_tarski(sK1,sK2)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f98])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k2_tarski(sK1,sK2)) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | sK0 = k2_tarski(sK1,sK2)),
% 0.21/0.52    inference(superposition,[],[f49,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | sK0 = k2_tarski(sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ((sK0 != k2_tarski(sK1,sK2) & sK0 != k1_tarski(sK2) & sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))) & (sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)))) => (((sK0 != k2_tarski(sK1,sK2) & sK0 != k1_tarski(sK2) & sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))) & (sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 0.21/0.52    inference(nnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <~> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.21/0.52    inference(negated_conjecture,[],[f21])).
% 0.21/0.52  fof(f21,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.52    inference(nnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ~r1_tarski(sK0,k2_tarski(sK1,sK2)) | sK0 != k2_tarski(sK1,sK2)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | sK0 != k2_tarski(sK1,sK2) | ~r1_tarski(sK0,k2_tarski(sK1,sK2))),
% 0.21/0.52    inference(superposition,[],[f37,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | sK0 != k2_tarski(sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    r1_tarski(sK0,sK0) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | sK0 = k1_tarski(sK2)),
% 0.21/0.52    inference(superposition,[],[f63,f100])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X2,X1] : (r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2))) )),
% 0.21/0.52    inference(equality_resolution,[],[f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X2) != X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | sK0 != k1_tarski(sK2)),
% 0.21/0.52    inference(resolution,[],[f127,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ~r1_tarski(sK0,k2_tarski(sK1,sK2)) | sK0 != k1_tarski(sK2)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | sK0 != k1_tarski(sK2) | ~r1_tarski(sK0,k2_tarski(sK1,sK2))),
% 0.21/0.52    inference(superposition,[],[f36,f50])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | sK0 != k1_tarski(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    ( ! [X5] : (r1_tarski(sK0,k2_tarski(X5,sK2)) | k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1)) )),
% 0.21/0.52    inference(superposition,[],[f64,f121])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X2,X1] : (r1_tarski(k1_tarski(X2),k2_tarski(X1,X2))) )),
% 0.21/0.52    inference(equality_resolution,[],[f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | sK0 != k1_tarski(sK1)),
% 0.21/0.52    inference(resolution,[],[f163,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ~r1_tarski(sK0,k2_tarski(sK1,sK2)) | sK0 != k1_tarski(sK1)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | sK0 != k1_tarski(sK1) | ~r1_tarski(sK0,k2_tarski(sK1,sK2))),
% 0.21/0.52    inference(superposition,[],[f35,f50])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | sK0 != k1_tarski(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    ( ! [X4] : (r1_tarski(sK0,k2_tarski(sK1,X4)) | k1_xboole_0 = sK0) )),
% 0.21/0.53    inference(superposition,[],[f65,f158])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X2,X1] : (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))) )),
% 0.21/0.53    inference(equality_resolution,[],[f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    ~r1_tarski(sK0,k2_tarski(sK1,sK2))),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f192])).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(sK0,k2_tarski(sK1,sK2))),
% 0.21/0.53    inference(backward_demodulation,[],[f69,f185])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ~r1_tarski(sK0,k2_tarski(sK1,sK2)) | k1_xboole_0 != sK0),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != sK0 | ~r1_tarski(sK0,k2_tarski(sK1,sK2))),
% 0.21/0.53    inference(superposition,[],[f34,f50])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | k1_xboole_0 != sK0),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (17662)------------------------------
% 0.21/0.53  % (17662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (17662)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (17662)Memory used [KB]: 1791
% 0.21/0.53  % (17662)Time elapsed: 0.066 s
% 0.21/0.53  % (17662)------------------------------
% 0.21/0.53  % (17662)------------------------------
% 0.21/0.53  % (17638)Success in time 0.163 s
%------------------------------------------------------------------------------
