%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:31 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 120 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :   19
%              Number of atoms          :  138 ( 356 expanded)
%              Number of equality atoms :   36 (  63 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f409,plain,(
    $false ),
    inference(resolution,[],[f405,f54])).

fof(f54,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

% (14781)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f6,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f405,plain,(
    ! [X0] : ~ r1_xboole_0(X0,X0) ),
    inference(subsumption_resolution,[],[f404,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f404,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0,sK0),X0)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f399,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f399,plain,(
    r2_hidden(sK4(k1_xboole_0,sK0),k1_xboole_0) ),
    inference(resolution,[],[f396,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f396,plain,(
    ~ r1_xboole_0(k1_xboole_0,sK0) ),
    inference(trivial_inequality_removal,[],[f393])).

fof(f393,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_xboole_0,sK0) ),
    inference(superposition,[],[f385,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f385,plain,(
    k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK0) ),
    inference(superposition,[],[f160,f352])).

fof(f352,plain,(
    k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f351,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f351,plain,(
    k3_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f341,f106])).

fof(f106,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK3)) ),
    inference(superposition,[],[f102,f38])).

fof(f102,plain,(
    k1_xboole_0 = k3_xboole_0(k1_tarski(sK3),sK1) ),
    inference(resolution,[],[f100,f46])).

fof(f100,plain,(
    r1_xboole_0(k1_tarski(sK3),sK1) ),
    inference(resolution,[],[f99,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f99,plain,(
    ~ r2_hidden(sK3,sK1) ),
    inference(resolution,[],[f59,f32])).

fof(f32,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f59,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f33,f43])).

fof(f33,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f341,plain,(
    k3_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k3_xboole_0(sK1,k1_tarski(sK3))) ),
    inference(superposition,[],[f80,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f80,plain,(
    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(resolution,[],[f31,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f31,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f160,plain,(
    k1_xboole_0 != k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f152,f38])).

fof(f152,plain,(
    k1_xboole_0 != k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f151,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f151,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f147,f64])).

fof(f64,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f58,f38])).

fof(f58,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f33,f46])).

fof(f147,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f127,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f127,plain,(
    k1_xboole_0 != k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f60,f38])).

fof(f60,plain,(
    k1_xboole_0 != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[],[f34,f47])).

fof(f34,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:54:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.41/0.55  % (14780)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.56  % (14772)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.57  % (14764)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.57  % (14760)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.41/0.58  % (14762)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.67/0.58  % (14770)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.67/0.58  % (14757)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.67/0.58  % (14758)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.67/0.58  % (14780)Refutation found. Thanks to Tanya!
% 1.67/0.58  % SZS status Theorem for theBenchmark
% 1.67/0.58  % SZS output start Proof for theBenchmark
% 1.67/0.58  fof(f409,plain,(
% 1.67/0.58    $false),
% 1.67/0.58    inference(resolution,[],[f405,f54])).
% 1.67/0.58  fof(f54,plain,(
% 1.67/0.58    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.67/0.58    inference(equality_resolution,[],[f36])).
% 1.67/0.58  fof(f36,plain,(
% 1.67/0.58    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f21])).
% 1.67/0.58  fof(f21,plain,(
% 1.67/0.58    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.67/0.58    inference(ennf_transformation,[],[f6])).
% 1.67/0.58  % (14781)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.67/0.58  fof(f6,axiom,(
% 1.67/0.58    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.67/0.58  fof(f405,plain,(
% 1.67/0.58    ( ! [X0] : (~r1_xboole_0(X0,X0)) )),
% 1.67/0.58    inference(subsumption_resolution,[],[f404,f43])).
% 1.67/0.58  fof(f43,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f29])).
% 1.67/0.58  fof(f29,plain,(
% 1.67/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.67/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f28])).
% 1.67/0.58  fof(f28,plain,(
% 1.67/0.58    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.67/0.58    introduced(choice_axiom,[])).
% 1.67/0.58  fof(f22,plain,(
% 1.67/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.67/0.58    inference(ennf_transformation,[],[f18])).
% 1.67/0.58  fof(f18,plain,(
% 1.67/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.67/0.58    inference(rectify,[],[f3])).
% 1.67/0.59  fof(f3,axiom,(
% 1.67/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.67/0.59  fof(f404,plain,(
% 1.67/0.59    ( ! [X0] : (r2_hidden(sK4(X0,sK0),X0) | ~r1_xboole_0(X0,X0)) )),
% 1.67/0.59    inference(superposition,[],[f399,f37])).
% 1.67/0.59  fof(f37,plain,(
% 1.67/0.59    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.67/0.59    inference(cnf_transformation,[],[f21])).
% 1.67/0.59  fof(f399,plain,(
% 1.67/0.59    r2_hidden(sK4(k1_xboole_0,sK0),k1_xboole_0)),
% 1.67/0.59    inference(resolution,[],[f396,f41])).
% 1.67/0.59  fof(f41,plain,(
% 1.67/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f29])).
% 1.67/0.59  fof(f396,plain,(
% 1.67/0.59    ~r1_xboole_0(k1_xboole_0,sK0)),
% 1.67/0.59    inference(trivial_inequality_removal,[],[f393])).
% 1.67/0.59  fof(f393,plain,(
% 1.67/0.59    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_xboole_0,sK0)),
% 1.67/0.59    inference(superposition,[],[f385,f46])).
% 1.67/0.59  fof(f46,plain,(
% 1.67/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f30])).
% 1.67/0.59  fof(f30,plain,(
% 1.67/0.59    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.67/0.59    inference(nnf_transformation,[],[f2])).
% 1.67/0.59  fof(f2,axiom,(
% 1.67/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.67/0.59  fof(f385,plain,(
% 1.67/0.59    k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK0)),
% 1.67/0.59    inference(superposition,[],[f160,f352])).
% 1.67/0.59  fof(f352,plain,(
% 1.67/0.59    k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_xboole_0,sK0)),
% 1.67/0.59    inference(forward_demodulation,[],[f351,f38])).
% 1.67/0.59  fof(f38,plain,(
% 1.67/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f1])).
% 1.67/0.59  fof(f1,axiom,(
% 1.67/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.67/0.59  fof(f351,plain,(
% 1.67/0.59    k3_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k1_xboole_0)),
% 1.67/0.59    inference(forward_demodulation,[],[f341,f106])).
% 1.67/0.59  fof(f106,plain,(
% 1.67/0.59    k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK3))),
% 1.67/0.59    inference(superposition,[],[f102,f38])).
% 1.67/0.59  fof(f102,plain,(
% 1.67/0.59    k1_xboole_0 = k3_xboole_0(k1_tarski(sK3),sK1)),
% 1.67/0.59    inference(resolution,[],[f100,f46])).
% 1.67/0.59  fof(f100,plain,(
% 1.67/0.59    r1_xboole_0(k1_tarski(sK3),sK1)),
% 1.67/0.59    inference(resolution,[],[f99,f44])).
% 1.67/0.59  fof(f44,plain,(
% 1.67/0.59    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f23])).
% 1.67/0.59  fof(f23,plain,(
% 1.67/0.59    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.67/0.59    inference(ennf_transformation,[],[f14])).
% 1.67/0.59  fof(f14,axiom,(
% 1.67/0.59    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.67/0.59  fof(f99,plain,(
% 1.67/0.59    ~r2_hidden(sK3,sK1)),
% 1.67/0.59    inference(resolution,[],[f59,f32])).
% 1.67/0.59  fof(f32,plain,(
% 1.67/0.59    r2_hidden(sK3,sK2)),
% 1.67/0.59    inference(cnf_transformation,[],[f27])).
% 1.67/0.59  fof(f27,plain,(
% 1.67/0.59    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.67/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f26])).
% 1.67/0.59  fof(f26,plain,(
% 1.67/0.59    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.67/0.59    introduced(choice_axiom,[])).
% 1.67/0.59  fof(f20,plain,(
% 1.67/0.59    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.67/0.59    inference(flattening,[],[f19])).
% 1.67/0.59  fof(f19,plain,(
% 1.67/0.59    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.67/0.59    inference(ennf_transformation,[],[f17])).
% 1.67/0.59  fof(f17,negated_conjecture,(
% 1.67/0.59    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.67/0.59    inference(negated_conjecture,[],[f16])).
% 1.67/0.59  fof(f16,conjecture,(
% 1.67/0.59    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.67/0.59  fof(f59,plain,(
% 1.67/0.59    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1)) )),
% 1.67/0.59    inference(resolution,[],[f33,f43])).
% 1.67/0.59  fof(f33,plain,(
% 1.67/0.59    r1_xboole_0(sK2,sK1)),
% 1.67/0.59    inference(cnf_transformation,[],[f27])).
% 1.67/0.59  fof(f341,plain,(
% 1.67/0.59    k3_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k3_xboole_0(sK1,k1_tarski(sK3)))),
% 1.67/0.59    inference(superposition,[],[f80,f49])).
% 1.67/0.59  fof(f49,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.67/0.59    inference(cnf_transformation,[],[f4])).
% 1.67/0.59  fof(f4,axiom,(
% 1.67/0.59    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.67/0.59  fof(f80,plain,(
% 1.67/0.59    k3_xboole_0(sK0,sK1) = k3_xboole_0(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.67/0.59    inference(resolution,[],[f31,f45])).
% 1.67/0.59  fof(f45,plain,(
% 1.67/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f24])).
% 1.67/0.59  fof(f24,plain,(
% 1.67/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.67/0.59    inference(ennf_transformation,[],[f5])).
% 1.67/0.59  fof(f5,axiom,(
% 1.67/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.67/0.59  fof(f31,plain,(
% 1.67/0.59    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.67/0.59    inference(cnf_transformation,[],[f27])).
% 1.67/0.59  fof(f160,plain,(
% 1.67/0.59    k1_xboole_0 != k3_xboole_0(sK0,sK1)),
% 1.67/0.59    inference(superposition,[],[f152,f38])).
% 1.67/0.59  fof(f152,plain,(
% 1.67/0.59    k1_xboole_0 != k3_xboole_0(sK1,sK0)),
% 1.67/0.59    inference(resolution,[],[f151,f47])).
% 1.67/0.59  fof(f47,plain,(
% 1.67/0.59    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.67/0.59    inference(cnf_transformation,[],[f30])).
% 1.67/0.59  fof(f151,plain,(
% 1.67/0.59    ~r1_xboole_0(sK1,sK0)),
% 1.67/0.59    inference(subsumption_resolution,[],[f147,f64])).
% 1.67/0.59  fof(f64,plain,(
% 1.67/0.59    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.67/0.59    inference(superposition,[],[f58,f38])).
% 1.67/0.59  fof(f58,plain,(
% 1.67/0.59    k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 1.67/0.59    inference(resolution,[],[f33,f46])).
% 1.67/0.59  fof(f147,plain,(
% 1.67/0.59    k1_xboole_0 != k3_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0)),
% 1.67/0.59    inference(superposition,[],[f127,f50])).
% 1.67/0.59  fof(f50,plain,(
% 1.67/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 1.67/0.59    inference(cnf_transformation,[],[f25])).
% 1.67/0.59  fof(f25,plain,(
% 1.67/0.59    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 1.67/0.59    inference(ennf_transformation,[],[f7])).
% 1.67/0.59  fof(f7,axiom,(
% 1.67/0.59    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 1.67/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 1.67/0.59  fof(f127,plain,(
% 1.67/0.59    k1_xboole_0 != k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 1.67/0.59    inference(superposition,[],[f60,f38])).
% 1.67/0.59  fof(f60,plain,(
% 1.67/0.59    k1_xboole_0 != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.67/0.59    inference(resolution,[],[f34,f47])).
% 1.67/0.59  fof(f34,plain,(
% 1.67/0.59    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.67/0.59    inference(cnf_transformation,[],[f27])).
% 1.67/0.59  % SZS output end Proof for theBenchmark
% 1.67/0.59  % (14780)------------------------------
% 1.67/0.59  % (14780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.59  % (14780)Termination reason: Refutation
% 1.67/0.59  
% 1.67/0.59  % (14780)Memory used [KB]: 1918
% 1.67/0.59  % (14780)Time elapsed: 0.097 s
% 1.67/0.59  % (14780)------------------------------
% 1.67/0.59  % (14780)------------------------------
% 1.67/0.59  % (14773)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.67/0.59  % (14761)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.67/0.59  % (14756)Success in time 0.227 s
%------------------------------------------------------------------------------
