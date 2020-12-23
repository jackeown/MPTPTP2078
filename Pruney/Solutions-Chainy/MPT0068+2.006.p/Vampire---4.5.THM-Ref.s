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
% DateTime   : Thu Dec  3 12:30:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   16 (  21 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  50 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18,f12])).

fof(f12,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f18,plain,(
    ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f17,f10])).

fof(f10,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,
    ( ~ r2_xboole_0(k1_xboole_0,sK0)
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f6])).

fof(f6,plain,
    ( ? [X0] :
        ( ~ r2_xboole_0(k1_xboole_0,X0)
        & k1_xboole_0 != X0 )
   => ( ~ r2_xboole_0(k1_xboole_0,sK0)
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
      ( ~ r2_xboole_0(k1_xboole_0,X0)
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => r2_xboole_0(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).

fof(f17,plain,
    ( k1_xboole_0 = sK0
    | ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(resolution,[],[f11,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f11,plain,(
    ~ r2_xboole_0(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f7])).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 16:01:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.47  % (17760)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (17762)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (17752)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (17752)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f18,f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ~r1_tarski(k1_xboole_0,sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f17,f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    k1_xboole_0 != sK0),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ~r2_xboole_0(k1_xboole_0,sK0) & k1_xboole_0 != sK0),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f6])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ? [X0] : (~r2_xboole_0(k1_xboole_0,X0) & k1_xboole_0 != X0) => (~r2_xboole_0(k1_xboole_0,sK0) & k1_xboole_0 != sK0)),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f5,plain,(
% 0.20/0.48    ? [X0] : (~r2_xboole_0(k1_xboole_0,X0) & k1_xboole_0 != X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,negated_conjecture,(
% 0.20/0.48    ~! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 0.20/0.48    inference(negated_conjecture,[],[f3])).
% 0.20/0.48  fof(f3,conjecture,(
% 0.20/0.48    ! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | ~r1_tarski(k1_xboole_0,sK0)),
% 0.20/0.48    inference(resolution,[],[f11,f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.48    inference(flattening,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ~r2_xboole_0(k1_xboole_0,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (17752)------------------------------
% 0.20/0.48  % (17752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17752)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (17752)Memory used [KB]: 1535
% 0.20/0.48  % (17752)Time elapsed: 0.055 s
% 0.20/0.48  % (17752)------------------------------
% 0.20/0.48  % (17752)------------------------------
% 0.20/0.48  % (17754)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (17739)Success in time 0.121 s
%------------------------------------------------------------------------------
