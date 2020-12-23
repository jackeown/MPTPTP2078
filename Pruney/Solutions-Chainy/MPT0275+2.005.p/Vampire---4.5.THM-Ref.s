%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 113 expanded)
%              Number of leaves         :    4 (  24 expanded)
%              Depth                    :   15
%              Number of atoms          :   99 ( 458 expanded)
%              Number of equality atoms :   28 ( 136 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f216,plain,(
    $false ),
    inference(subsumption_resolution,[],[f211,f196])).

fof(f196,plain,(
    r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f194,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f194,plain,(
    r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(trivial_inequality_removal,[],[f192])).

fof(f192,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(superposition,[],[f66,f153])).

fof(f153,plain,(
    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f152,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f152,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(resolution,[],[f89,f44])).

fof(f44,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( r2_hidden(sK1,sK2)
        & r2_hidden(sK0,sK2) )
      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK0,sK2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( r2_hidden(sK1,sK2)
          & r2_hidden(sK0,sK2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f89,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r1_tarski(k2_tarski(X0,sK1),sK2)
      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(resolution,[],[f45,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f45,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f211,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f197,f155])).

fof(f155,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f154])).

fof(f154,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(backward_demodulation,[],[f46,f153])).

fof(f46,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f197,plain,(
    r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f194,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (23462)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.47  % (23454)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.48  % (23445)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (23454)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f211,f196])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    r2_hidden(sK0,sK2)),
% 0.21/0.49    inference(resolution,[],[f194,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.49    inference(flattening,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.49    inference(nnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f192])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    k1_xboole_0 != k1_xboole_0 | r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.49    inference(superposition,[],[f66,f153])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f152,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    r1_tarski(k2_tarski(sK0,sK1),sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f143])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    r1_tarski(k2_tarski(sK0,sK1),sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.49    inference(resolution,[],[f89,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    r2_hidden(sK0,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    (~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.49    inference(flattening,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.49    inference(nnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.49    inference(negated_conjecture,[],[f20])).
% 0.21/0.49  fof(f20,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK2) | r1_tarski(k2_tarski(X0,sK1),sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)) )),
% 0.21/0.49    inference(resolution,[],[f45,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    r2_hidden(sK1,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    ~r2_hidden(sK0,sK2)),
% 0.21/0.49    inference(resolution,[],[f197,f155])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f154])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2)),
% 0.21/0.49    inference(backward_demodulation,[],[f46,f153])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    r2_hidden(sK1,sK2)),
% 0.21/0.49    inference(resolution,[],[f194,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (23454)------------------------------
% 0.21/0.49  % (23454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (23454)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (23454)Memory used [KB]: 1791
% 0.21/0.49  % (23454)Time elapsed: 0.055 s
% 0.21/0.49  % (23454)------------------------------
% 0.21/0.49  % (23454)------------------------------
% 0.21/0.50  % (23435)Success in time 0.135 s
%------------------------------------------------------------------------------
