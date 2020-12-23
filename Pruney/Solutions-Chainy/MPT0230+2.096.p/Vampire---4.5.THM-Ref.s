%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:47 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 131 expanded)
%              Number of leaves         :   10 (  33 expanded)
%              Depth                    :   15
%              Number of atoms          :  202 ( 536 expanded)
%              Number of equality atoms :  119 ( 340 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(subsumption_resolution,[],[f134,f47])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f134,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f122,f110])).

fof(f110,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(superposition,[],[f56,f101])).

fof(f101,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f100,f27])).

fof(f27,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK0 != sK2
    & sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK0 != sK2
      & sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f100,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK2 ),
    inference(subsumption_resolution,[],[f99,f26])).

fof(f26,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f99,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | sK0 = sK1
    | sK0 = sK2 ),
    inference(resolution,[],[f97,f53])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

% (4670)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f97,plain,
    ( r2_hidden(sK0,k2_tarski(sK1,sK2))
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(resolution,[],[f62,f25])).

fof(f25,plain,(
    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_tarski(X2),X3)
      | r2_hidden(X2,X3)
      | k1_xboole_0 = k1_tarski(X2) ) ),
    inference(superposition,[],[f55,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f55,plain,(
    ! [X2,X1] :
      ( k1_tarski(X1) = k4_xboole_0(k1_tarski(X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(forward_demodulation,[],[f54,f28])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X2,X1] :
      ( k1_tarski(X1) = k4_xboole_0(k2_tarski(X1,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f56,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f52,f28])).

fof(f52,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f51])).

% (4669)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f51,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f119,f72])).

fof(f72,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k5_xboole_0(X2,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f65])).

fof(f65,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k5_xboole_0(X2,X2)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f59,f36])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f29,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f119,plain,(
    ! [X0] :
      ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(sK0,X0)
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f107,f59])).

fof(f107,plain,(
    ! [X1] :
      ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,X1)
      | ~ r2_hidden(sK0,X1) ) ),
    inference(superposition,[],[f73,f101])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f43,f28])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:35:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (4684)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.50  % (4684)Refutation not found, incomplete strategy% (4684)------------------------------
% 0.21/0.50  % (4684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4672)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (4684)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4684)Memory used [KB]: 1663
% 0.21/0.51  % (4684)Time elapsed: 0.094 s
% 0.21/0.51  % (4684)------------------------------
% 0.21/0.51  % (4684)------------------------------
% 0.21/0.51  % (4676)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.24/0.51  % (4674)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.24/0.51  % (4675)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.24/0.51  % (4681)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.24/0.51  % (4681)Refutation not found, incomplete strategy% (4681)------------------------------
% 1.24/0.51  % (4681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.51  % (4681)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.51  
% 1.24/0.51  % (4681)Memory used [KB]: 1663
% 1.24/0.51  % (4681)Time elapsed: 0.074 s
% 1.24/0.51  % (4681)------------------------------
% 1.24/0.51  % (4681)------------------------------
% 1.24/0.52  % (4676)Refutation found. Thanks to Tanya!
% 1.24/0.52  % SZS status Theorem for theBenchmark
% 1.24/0.52  % SZS output start Proof for theBenchmark
% 1.24/0.52  fof(f139,plain,(
% 1.24/0.52    $false),
% 1.24/0.52    inference(subsumption_resolution,[],[f134,f47])).
% 1.24/0.52  fof(f47,plain,(
% 1.24/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.24/0.52    inference(equality_resolution,[],[f33])).
% 1.24/0.52  fof(f33,plain,(
% 1.24/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.24/0.52    inference(cnf_transformation,[],[f16])).
% 1.24/0.52  fof(f16,plain,(
% 1.24/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.24/0.52    inference(flattening,[],[f15])).
% 1.24/0.52  fof(f15,plain,(
% 1.24/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.24/0.52    inference(nnf_transformation,[],[f1])).
% 1.24/0.52  fof(f1,axiom,(
% 1.24/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.24/0.52  fof(f134,plain,(
% 1.24/0.52    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.24/0.52    inference(resolution,[],[f122,f110])).
% 1.24/0.52  fof(f110,plain,(
% 1.24/0.52    r2_hidden(sK0,k1_xboole_0)),
% 1.24/0.52    inference(superposition,[],[f56,f101])).
% 1.24/0.52  fof(f101,plain,(
% 1.24/0.52    k1_xboole_0 = k1_tarski(sK0)),
% 1.24/0.52    inference(subsumption_resolution,[],[f100,f27])).
% 1.24/0.52  fof(f27,plain,(
% 1.24/0.52    sK0 != sK2),
% 1.24/0.52    inference(cnf_transformation,[],[f14])).
% 1.24/0.52  fof(f14,plain,(
% 1.24/0.52    sK0 != sK2 & sK0 != sK1 & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.24/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 1.24/0.52  fof(f13,plain,(
% 1.24/0.52    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK0 != sK2 & sK0 != sK1 & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)))),
% 1.24/0.52    introduced(choice_axiom,[])).
% 1.24/0.52  fof(f11,plain,(
% 1.24/0.52    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.24/0.52    inference(ennf_transformation,[],[f10])).
% 1.24/0.52  fof(f10,negated_conjecture,(
% 1.24/0.52    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.24/0.52    inference(negated_conjecture,[],[f9])).
% 1.24/0.52  fof(f9,conjecture,(
% 1.24/0.52    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 1.24/0.52  fof(f100,plain,(
% 1.24/0.52    k1_xboole_0 = k1_tarski(sK0) | sK0 = sK2),
% 1.24/0.52    inference(subsumption_resolution,[],[f99,f26])).
% 1.24/0.52  fof(f26,plain,(
% 1.24/0.52    sK0 != sK1),
% 1.24/0.52    inference(cnf_transformation,[],[f14])).
% 1.24/0.52  fof(f99,plain,(
% 1.24/0.52    k1_xboole_0 = k1_tarski(sK0) | sK0 = sK1 | sK0 = sK2),
% 1.24/0.52    inference(resolution,[],[f97,f53])).
% 1.24/0.52  fof(f53,plain,(
% 1.24/0.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 1.24/0.52    inference(equality_resolution,[],[f37])).
% 1.24/0.52  fof(f37,plain,(
% 1.24/0.52    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.24/0.52    inference(cnf_transformation,[],[f22])).
% 1.24/0.52  fof(f22,plain,(
% 1.24/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.24/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).
% 1.24/0.52  % (4670)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.24/0.52  fof(f21,plain,(
% 1.24/0.52    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.24/0.52    introduced(choice_axiom,[])).
% 1.24/0.52  fof(f20,plain,(
% 1.24/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.24/0.52    inference(rectify,[],[f19])).
% 1.24/0.52  fof(f19,plain,(
% 1.24/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.24/0.52    inference(flattening,[],[f18])).
% 1.24/0.52  fof(f18,plain,(
% 1.24/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.24/0.52    inference(nnf_transformation,[],[f5])).
% 1.24/0.52  fof(f5,axiom,(
% 1.24/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.24/0.52  fof(f97,plain,(
% 1.24/0.52    r2_hidden(sK0,k2_tarski(sK1,sK2)) | k1_xboole_0 = k1_tarski(sK0)),
% 1.24/0.52    inference(resolution,[],[f62,f25])).
% 1.24/0.52  fof(f25,plain,(
% 1.24/0.52    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.24/0.52    inference(cnf_transformation,[],[f14])).
% 1.24/0.52  fof(f62,plain,(
% 1.24/0.52    ( ! [X2,X3] : (~r1_tarski(k1_tarski(X2),X3) | r2_hidden(X2,X3) | k1_xboole_0 = k1_tarski(X2)) )),
% 1.24/0.52    inference(superposition,[],[f55,f36])).
% 1.24/0.52  fof(f36,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f17])).
% 1.24/0.52  fof(f17,plain,(
% 1.24/0.52    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.24/0.52    inference(nnf_transformation,[],[f2])).
% 1.24/0.52  fof(f2,axiom,(
% 1.24/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.24/0.52  fof(f55,plain,(
% 1.24/0.52    ( ! [X2,X1] : (k1_tarski(X1) = k4_xboole_0(k1_tarski(X1),X2) | r2_hidden(X1,X2)) )),
% 1.24/0.52    inference(forward_demodulation,[],[f54,f28])).
% 1.24/0.52  fof(f28,plain,(
% 1.24/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f6])).
% 1.24/0.52  fof(f6,axiom,(
% 1.24/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.24/0.52  fof(f54,plain,(
% 1.24/0.52    ( ! [X2,X1] : (k1_tarski(X1) = k4_xboole_0(k2_tarski(X1,X1),X2) | r2_hidden(X1,X2)) )),
% 1.24/0.52    inference(equality_resolution,[],[f46])).
% 1.24/0.52  fof(f46,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | X0 != X1 | r2_hidden(X0,X2)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f24])).
% 1.24/0.52  fof(f24,plain,(
% 1.24/0.52    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.24/0.52    inference(flattening,[],[f23])).
% 1.24/0.52  fof(f23,plain,(
% 1.24/0.52    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.24/0.52    inference(nnf_transformation,[],[f8])).
% 1.24/0.52  fof(f8,axiom,(
% 1.24/0.52    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 1.24/0.52  fof(f56,plain,(
% 1.24/0.52    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 1.24/0.52    inference(superposition,[],[f52,f28])).
% 1.24/0.52  fof(f52,plain,(
% 1.24/0.52    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 1.24/0.52    inference(equality_resolution,[],[f51])).
% 1.24/0.52  % (4669)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.24/0.52  fof(f51,plain,(
% 1.24/0.52    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 1.24/0.52    inference(equality_resolution,[],[f38])).
% 1.24/0.52  fof(f38,plain,(
% 1.24/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.24/0.52    inference(cnf_transformation,[],[f22])).
% 1.24/0.52  fof(f122,plain,(
% 1.24/0.52    ( ! [X0] : (~r2_hidden(sK0,X0) | ~r1_tarski(k1_xboole_0,X0)) )),
% 1.24/0.52    inference(subsumption_resolution,[],[f119,f72])).
% 1.24/0.52  fof(f72,plain,(
% 1.24/0.52    ( ! [X2,X3] : (k1_xboole_0 = k5_xboole_0(X2,X2) | ~r1_tarski(X2,X3)) )),
% 1.24/0.52    inference(duplicate_literal_removal,[],[f65])).
% 1.24/0.52  fof(f65,plain,(
% 1.24/0.52    ( ! [X2,X3] : (k1_xboole_0 = k5_xboole_0(X2,X2) | ~r1_tarski(X2,X3) | ~r1_tarski(X2,X3)) )),
% 1.24/0.52    inference(superposition,[],[f59,f36])).
% 1.24/0.52  fof(f59,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X1)) )),
% 1.24/0.52    inference(superposition,[],[f29,f31])).
% 1.24/0.52  fof(f31,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f12])).
% 1.24/0.52  fof(f12,plain,(
% 1.24/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.24/0.52    inference(ennf_transformation,[],[f4])).
% 1.24/0.52  fof(f4,axiom,(
% 1.24/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.24/0.52  fof(f29,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.24/0.52    inference(cnf_transformation,[],[f3])).
% 1.24/0.52  fof(f3,axiom,(
% 1.24/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.24/0.52  fof(f119,plain,(
% 1.24/0.52    ( ! [X0] : (k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~r2_hidden(sK0,X0) | ~r1_tarski(k1_xboole_0,X0)) )),
% 1.24/0.52    inference(superposition,[],[f107,f59])).
% 1.24/0.52  fof(f107,plain,(
% 1.24/0.52    ( ! [X1] : (k1_xboole_0 != k4_xboole_0(k1_xboole_0,X1) | ~r2_hidden(sK0,X1)) )),
% 1.24/0.52    inference(superposition,[],[f73,f101])).
% 1.24/0.52  fof(f73,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.24/0.52    inference(superposition,[],[f43,f28])).
% 1.24/0.52  fof(f43,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f24])).
% 1.24/0.52  % SZS output end Proof for theBenchmark
% 1.24/0.52  % (4676)------------------------------
% 1.24/0.52  % (4676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (4676)Termination reason: Refutation
% 1.24/0.52  
% 1.24/0.52  % (4676)Memory used [KB]: 1791
% 1.24/0.52  % (4676)Time elapsed: 0.108 s
% 1.24/0.52  % (4676)------------------------------
% 1.24/0.52  % (4676)------------------------------
% 1.24/0.52  % (4667)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.24/0.52  % (4668)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.24/0.52  % (4692)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.24/0.52  % (4666)Success in time 0.165 s
%------------------------------------------------------------------------------
