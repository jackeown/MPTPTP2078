%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:05 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 187 expanded)
%              Number of leaves         :    9 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  142 ( 707 expanded)
%              Number of equality atoms :   66 ( 394 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(resolution,[],[f80,f82])).

fof(f82,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f71,f70])).

fof(f70,plain,(
    r1_xboole_0(k1_xboole_0,k1_tarski(sK1)) ),
    inference(trivial_inequality_removal,[],[f69])).

fof(f69,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f56,f65])).

fof(f65,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f64,f32])).

fof(f32,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f64,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f63,f49])).

fof(f49,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f63,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(superposition,[],[f48,f52])).

fof(f52,plain,
    ( k1_tarski(sK0) = k1_tarski(sK1)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(resolution,[],[f31,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f31,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | r1_xboole_0(k1_xboole_0,k1_tarski(sK1)) ),
    inference(inner_rewriting,[],[f54])).

fof(f54,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(superposition,[],[f45,f53])).

fof(f53,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(resolution,[],[f31,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
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

fof(f71,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_xboole_0,k1_tarski(sK1))
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f68,f65])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    inference(backward_demodulation,[],[f55,f65])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    inference(superposition,[],[f43,f53])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f80,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(superposition,[],[f48,f65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:52:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.20/0.51  % (28489)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.20/0.51  % (28488)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.20/0.52  % (28486)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.20/0.52  % (28506)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.20/0.52  % (28498)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.20/0.52  % (28508)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.20/0.53  % (28491)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.20/0.53  % (28498)Refutation found. Thanks to Tanya!
% 1.20/0.53  % SZS status Theorem for theBenchmark
% 1.20/0.53  % SZS output start Proof for theBenchmark
% 1.20/0.53  fof(f86,plain,(
% 1.20/0.53    $false),
% 1.20/0.53    inference(resolution,[],[f80,f82])).
% 1.20/0.53  fof(f82,plain,(
% 1.20/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.20/0.53    inference(resolution,[],[f71,f70])).
% 1.20/0.53  fof(f70,plain,(
% 1.20/0.53    r1_xboole_0(k1_xboole_0,k1_tarski(sK1))),
% 1.20/0.53    inference(trivial_inequality_removal,[],[f69])).
% 1.20/0.53  fof(f69,plain,(
% 1.20/0.53    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,k1_tarski(sK1))),
% 1.20/0.53    inference(backward_demodulation,[],[f56,f65])).
% 1.20/0.53  fof(f65,plain,(
% 1.20/0.53    k1_xboole_0 = k1_tarski(sK0)),
% 1.20/0.53    inference(subsumption_resolution,[],[f64,f32])).
% 1.20/0.53  fof(f32,plain,(
% 1.20/0.53    sK0 != sK1),
% 1.20/0.53    inference(cnf_transformation,[],[f21])).
% 1.20/0.53  fof(f21,plain,(
% 1.20/0.53    sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 1.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f20])).
% 1.20/0.53  fof(f20,plain,(
% 1.20/0.53    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.20/0.53    introduced(choice_axiom,[])).
% 1.20/0.53  fof(f17,plain,(
% 1.20/0.53    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.20/0.53    inference(ennf_transformation,[],[f15])).
% 1.20/0.53  fof(f15,negated_conjecture,(
% 1.20/0.53    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.20/0.53    inference(negated_conjecture,[],[f14])).
% 1.20/0.53  fof(f14,conjecture,(
% 1.20/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 1.20/0.53  fof(f64,plain,(
% 1.20/0.53    k1_xboole_0 = k1_tarski(sK0) | sK0 = sK1),
% 1.20/0.53    inference(resolution,[],[f63,f49])).
% 1.20/0.53  fof(f49,plain,(
% 1.20/0.53    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.20/0.53    inference(equality_resolution,[],[f33])).
% 1.20/0.53  fof(f33,plain,(
% 1.20/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.20/0.53    inference(cnf_transformation,[],[f25])).
% 1.20/0.53  fof(f25,plain,(
% 1.20/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).
% 1.20/0.53  fof(f24,plain,(
% 1.20/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.20/0.53    introduced(choice_axiom,[])).
% 1.20/0.53  fof(f23,plain,(
% 1.20/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.20/0.53    inference(rectify,[],[f22])).
% 1.20/0.53  fof(f22,plain,(
% 1.20/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.20/0.53    inference(nnf_transformation,[],[f5])).
% 1.20/0.53  fof(f5,axiom,(
% 1.20/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.20/0.53  fof(f63,plain,(
% 1.20/0.53    r2_hidden(sK1,k1_tarski(sK0)) | k1_xboole_0 = k1_tarski(sK0)),
% 1.20/0.53    inference(superposition,[],[f48,f52])).
% 1.20/0.53  fof(f52,plain,(
% 1.20/0.53    k1_tarski(sK0) = k1_tarski(sK1) | k1_xboole_0 = k1_tarski(sK0)),
% 1.20/0.53    inference(resolution,[],[f31,f38])).
% 1.20/0.53  fof(f38,plain,(
% 1.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.20/0.53    inference(cnf_transformation,[],[f27])).
% 1.20/0.53  fof(f27,plain,(
% 1.20/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.20/0.53    inference(flattening,[],[f26])).
% 1.20/0.53  fof(f26,plain,(
% 1.20/0.53    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.20/0.53    inference(nnf_transformation,[],[f13])).
% 1.20/0.53  fof(f13,axiom,(
% 1.20/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.20/0.53  fof(f31,plain,(
% 1.20/0.53    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 1.20/0.53    inference(cnf_transformation,[],[f21])).
% 1.20/0.53  fof(f48,plain,(
% 1.20/0.53    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.20/0.53    inference(equality_resolution,[],[f47])).
% 1.20/0.53  fof(f47,plain,(
% 1.20/0.53    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.20/0.53    inference(equality_resolution,[],[f34])).
% 1.20/0.53  fof(f34,plain,(
% 1.20/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.20/0.53    inference(cnf_transformation,[],[f25])).
% 1.20/0.53  fof(f56,plain,(
% 1.20/0.53    k1_xboole_0 != k1_tarski(sK0) | r1_xboole_0(k1_xboole_0,k1_tarski(sK1))),
% 1.20/0.53    inference(inner_rewriting,[],[f54])).
% 1.20/0.53  fof(f54,plain,(
% 1.20/0.53    k1_xboole_0 != k1_tarski(sK0) | r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.20/0.53    inference(superposition,[],[f45,f53])).
% 1.20/0.53  fof(f53,plain,(
% 1.20/0.53    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.20/0.53    inference(resolution,[],[f31,f37])).
% 1.20/0.53  fof(f37,plain,(
% 1.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.20/0.53    inference(cnf_transformation,[],[f18])).
% 1.20/0.53  fof(f18,plain,(
% 1.20/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.20/0.53    inference(ennf_transformation,[],[f4])).
% 1.20/0.53  fof(f4,axiom,(
% 1.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.20/0.53  fof(f45,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f30])).
% 1.20/0.53  fof(f30,plain,(
% 1.20/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.20/0.53    inference(nnf_transformation,[],[f2])).
% 1.20/0.53  fof(f2,axiom,(
% 1.20/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.20/0.53  fof(f71,plain,(
% 1.20/0.53    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,k1_tarski(sK1)) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.20/0.53    inference(forward_demodulation,[],[f68,f65])).
% 1.20/0.53  fof(f68,plain,(
% 1.20/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) )),
% 1.20/0.53    inference(backward_demodulation,[],[f55,f65])).
% 1.20/0.53  fof(f55,plain,(
% 1.20/0.53    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) )),
% 1.20/0.53    inference(superposition,[],[f43,f53])).
% 1.20/0.53  fof(f43,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f29])).
% 1.20/0.53  fof(f29,plain,(
% 1.20/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f28])).
% 1.20/0.53  fof(f28,plain,(
% 1.20/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.20/0.53    introduced(choice_axiom,[])).
% 1.20/0.53  fof(f19,plain,(
% 1.20/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.20/0.53    inference(ennf_transformation,[],[f16])).
% 1.20/0.53  fof(f16,plain,(
% 1.20/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.20/0.53    inference(rectify,[],[f3])).
% 1.20/0.53  fof(f3,axiom,(
% 1.20/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.20/0.53  fof(f80,plain,(
% 1.20/0.53    r2_hidden(sK0,k1_xboole_0)),
% 1.20/0.53    inference(superposition,[],[f48,f65])).
% 1.20/0.53  % SZS output end Proof for theBenchmark
% 1.20/0.53  % (28498)------------------------------
% 1.20/0.53  % (28498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (28498)Termination reason: Refutation
% 1.20/0.53  
% 1.20/0.53  % (28498)Memory used [KB]: 1663
% 1.20/0.53  % (28498)Time elapsed: 0.084 s
% 1.20/0.53  % (28498)------------------------------
% 1.20/0.53  % (28498)------------------------------
% 1.20/0.53  % (28500)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.20/0.53  % (28490)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.20/0.53  % (28503)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.20/0.53  % (28510)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.20/0.53  % (28487)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.20/0.53  % (28485)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.20/0.53  % (28505)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.20/0.53  % (28483)Success in time 0.167 s
%------------------------------------------------------------------------------
