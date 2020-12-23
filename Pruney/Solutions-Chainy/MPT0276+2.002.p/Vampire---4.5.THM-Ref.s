%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   36 (  80 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  116 ( 313 expanded)
%              Number of equality atoms :   58 ( 210 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(subsumption_resolution,[],[f200,f108])).

fof(f108,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f104,f75])).

% (25504)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f75,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f64])).

fof(f64,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(superposition,[],[f18,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f18,plain,(
    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f11])).

% (25502)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f11,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
    & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
   => ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
      & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f8])).

% (25496)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
          & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f7])).

% (25513)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_zfmisc_1)).

fof(f104,plain,
    ( ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f90])).

fof(f90,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | ~ r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2) ),
    inference(superposition,[],[f19,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f19,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f200,plain,(
    r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f197,f134])).

fof(f134,plain,(
    r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f131,f108])).

fof(f131,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f114])).

fof(f114,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2) ),
    inference(superposition,[],[f21,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f21,plain,(
    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f197,plain,
    ( ~ r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(trivial_inequality_removal,[],[f177])).

fof(f177,plain,
    ( k1_tarski(sK1) != k1_tarski(sK1)
    | ~ r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2) ),
    inference(superposition,[],[f20,f85])).

fof(f85,plain,(
    ! [X4,X2,X3] :
      ( k4_xboole_0(k2_tarski(X3,X2),X4) = k1_tarski(X2)
      | ~ r2_hidden(X3,X4)
      | r2_hidden(X2,X4) ) ),
    inference(superposition,[],[f30,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f20,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:53:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (25518)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (25510)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (25505)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (25510)Refutation not found, incomplete strategy% (25510)------------------------------
% 0.21/0.51  % (25510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (25510)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (25510)Memory used [KB]: 1663
% 0.21/0.51  % (25510)Time elapsed: 0.056 s
% 0.21/0.51  % (25510)------------------------------
% 0.21/0.51  % (25510)------------------------------
% 0.21/0.52  % (25505)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 1.24/0.52  % (25506)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.24/0.52  % SZS output start Proof for theBenchmark
% 1.24/0.52  fof(f201,plain,(
% 1.24/0.52    $false),
% 1.24/0.52    inference(subsumption_resolution,[],[f200,f108])).
% 1.24/0.52  fof(f108,plain,(
% 1.24/0.52    ~r2_hidden(sK1,sK2)),
% 1.24/0.52    inference(subsumption_resolution,[],[f104,f75])).
% 1.24/0.52  % (25504)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.24/0.52  fof(f75,plain,(
% 1.24/0.52    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2)),
% 1.24/0.52    inference(trivial_inequality_removal,[],[f64])).
% 1.24/0.52  fof(f64,plain,(
% 1.24/0.52    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2)),
% 1.24/0.52    inference(superposition,[],[f18,f27])).
% 1.24/0.52  fof(f27,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f13])).
% 1.24/0.52  fof(f13,plain,(
% 1.24/0.52    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0))),
% 1.24/0.52    inference(flattening,[],[f12])).
% 1.24/0.52  fof(f12,plain,(
% 1.24/0.52    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0))),
% 1.24/0.52    inference(nnf_transformation,[],[f6])).
% 1.24/0.52  fof(f6,axiom,(
% 1.24/0.52    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 1.24/0.52  fof(f18,plain,(
% 1.24/0.52    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.24/0.52    inference(cnf_transformation,[],[f11])).
% 1.24/0.52  % (25502)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.24/0.52  fof(f11,plain,(
% 1.24/0.52    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.24/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f10])).
% 1.24/0.52  fof(f10,plain,(
% 1.24/0.52    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0) => (k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 1.24/0.52    introduced(choice_axiom,[])).
% 1.24/0.52  fof(f9,plain,(
% 1.24/0.52    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0)),
% 1.24/0.52    inference(ennf_transformation,[],[f8])).
% 1.24/0.52  % (25496)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.24/0.52  fof(f8,negated_conjecture,(
% 1.24/0.52    ~! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0)),
% 1.24/0.52    inference(negated_conjecture,[],[f7])).
% 1.24/0.52  % (25513)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.24/0.52  fof(f7,conjecture,(
% 1.24/0.52    ! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0)),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_zfmisc_1)).
% 1.24/0.52  fof(f104,plain,(
% 1.24/0.52    ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2)),
% 1.24/0.52    inference(trivial_inequality_removal,[],[f90])).
% 1.24/0.52  fof(f90,plain,(
% 1.24/0.52    k1_tarski(sK0) != k1_tarski(sK0) | ~r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2)),
% 1.24/0.52    inference(superposition,[],[f19,f30])).
% 1.24/0.52  fof(f30,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f15])).
% 1.24/0.52  fof(f15,plain,(
% 1.24/0.52    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.24/0.52    inference(flattening,[],[f14])).
% 1.24/0.52  fof(f14,plain,(
% 1.24/0.52    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.24/0.52    inference(nnf_transformation,[],[f4])).
% 1.24/0.52  fof(f4,axiom,(
% 1.24/0.52    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 1.24/0.52  fof(f19,plain,(
% 1.24/0.52    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)),
% 1.24/0.52    inference(cnf_transformation,[],[f11])).
% 1.24/0.52  fof(f200,plain,(
% 1.24/0.52    r2_hidden(sK1,sK2)),
% 1.24/0.52    inference(subsumption_resolution,[],[f197,f134])).
% 1.24/0.52  fof(f134,plain,(
% 1.24/0.52    r2_hidden(sK0,sK2)),
% 1.24/0.52    inference(subsumption_resolution,[],[f131,f108])).
% 1.24/0.52  fof(f131,plain,(
% 1.24/0.52    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2)),
% 1.24/0.52    inference(trivial_inequality_removal,[],[f114])).
% 1.24/0.52  fof(f114,plain,(
% 1.24/0.52    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2)),
% 1.24/0.52    inference(superposition,[],[f21,f34])).
% 1.24/0.52  fof(f34,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f17])).
% 1.24/0.52  fof(f17,plain,(
% 1.24/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.24/0.52    inference(flattening,[],[f16])).
% 1.24/0.52  fof(f16,plain,(
% 1.24/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.24/0.52    inference(nnf_transformation,[],[f5])).
% 1.24/0.52  fof(f5,axiom,(
% 1.24/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 1.24/0.52  fof(f21,plain,(
% 1.24/0.52    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.24/0.52    inference(cnf_transformation,[],[f11])).
% 1.24/0.52  fof(f197,plain,(
% 1.24/0.52    ~r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2)),
% 1.24/0.52    inference(trivial_inequality_removal,[],[f177])).
% 1.24/0.52  fof(f177,plain,(
% 1.24/0.52    k1_tarski(sK1) != k1_tarski(sK1) | ~r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2)),
% 1.24/0.52    inference(superposition,[],[f20,f85])).
% 1.24/0.52  fof(f85,plain,(
% 1.24/0.52    ( ! [X4,X2,X3] : (k4_xboole_0(k2_tarski(X3,X2),X4) = k1_tarski(X2) | ~r2_hidden(X3,X4) | r2_hidden(X2,X4)) )),
% 1.24/0.52    inference(superposition,[],[f30,f23])).
% 1.24/0.52  fof(f23,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f1])).
% 1.24/0.52  fof(f1,axiom,(
% 1.24/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.24/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.24/0.52  fof(f20,plain,(
% 1.24/0.52    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)),
% 1.24/0.52    inference(cnf_transformation,[],[f11])).
% 1.24/0.52  % SZS output end Proof for theBenchmark
% 1.24/0.52  % (25505)------------------------------
% 1.24/0.52  % (25505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (25505)Termination reason: Refutation
% 1.24/0.52  
% 1.24/0.52  % (25505)Memory used [KB]: 1791
% 1.24/0.52  % (25505)Time elapsed: 0.099 s
% 1.24/0.52  % (25505)------------------------------
% 1.24/0.52  % (25505)------------------------------
% 1.24/0.52  % (25495)Success in time 0.161 s
%------------------------------------------------------------------------------
