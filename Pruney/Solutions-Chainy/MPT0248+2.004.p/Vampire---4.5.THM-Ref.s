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
% DateTime   : Thu Dec  3 12:37:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 317 expanded)
%              Number of leaves         :    8 (  84 expanded)
%              Depth                    :   19
%              Number of atoms          :  155 (1395 expanded)
%              Number of equality atoms :  118 (1246 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f265,plain,(
    $false ),
    inference(subsumption_resolution,[],[f264,f37])).

fof(f37,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f264,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f260,f236])).

fof(f236,plain,(
    k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f228])).

fof(f228,plain,
    ( sK2 != sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f194,f151])).

fof(f151,plain,
    ( sK2 = k1_tarski(sK0)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f145,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f145,plain,(
    r1_tarski(sK2,k1_tarski(sK0)) ),
    inference(superposition,[],[f127,f20])).

fof(f20,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f127,plain,(
    ! [X4,X5] : r1_tarski(X4,k2_xboole_0(X5,X4)) ),
    inference(superposition,[],[f25,f86])).

fof(f86,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f43,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f27,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f194,plain,(
    sK2 != k1_tarski(sK0) ),
    inference(trivial_inequality_removal,[],[f177])).

fof(f177,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK2 != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f22,f174])).

fof(f174,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f173,f79])).

fof(f79,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(trivial_inequality_removal,[],[f75])).

fof(f75,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f23,f68])).

fof(f68,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f25,f20])).

fof(f23,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f15])).

fof(f173,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f172,f80])).

fof(f80,plain,
    ( k1_xboole_0 = sK1
    | sK1 != sK2 ),
    inference(trivial_inequality_removal,[],[f74])).

fof(f74,plain,
    ( sK1 != sK2
    | sK1 != sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f21,f68])).

fof(f21,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f172,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | sK1 = sK2 ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | sK1 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f153,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | k1_xboole_0 = X0
      | sK1 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f33,f68])).

fof(f153,plain,
    ( r1_tarski(sK2,sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f145,f68])).

fof(f22,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f260,plain,(
    ~ r1_tarski(k1_xboole_0,sK2) ),
    inference(trivial_inequality_removal,[],[f241])).

fof(f241,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f104,f236])).

fof(f104,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 != sK2 ),
    inference(trivial_inequality_removal,[],[f99])).

fof(f99,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(superposition,[],[f59,f79])).

fof(f59,plain,
    ( ~ r1_tarski(sK1,sK2)
    | k1_xboole_0 != sK1 ),
    inference(trivial_inequality_removal,[],[f57])).

fof(f57,plain,
    ( sK2 != sK2
    | k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,sK2) ),
    inference(superposition,[],[f22,f46])).

fof(f46,plain,
    ( sK2 = k1_tarski(sK0)
    | ~ r1_tarski(sK1,sK2) ),
    inference(superposition,[],[f29,f20])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:56:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.22/0.50  % (19588)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.50  % (19609)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.51  % (19590)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.51  % (19601)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.51  % (19604)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.51  % (19585)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (19590)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (19596)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.51  % (19583)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (19584)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (19586)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (19609)Refutation not found, incomplete strategy% (19609)------------------------------
% 0.22/0.52  % (19609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19609)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19609)Memory used [KB]: 10746
% 0.22/0.52  % (19609)Time elapsed: 0.114 s
% 0.22/0.52  % (19609)------------------------------
% 0.22/0.52  % (19609)------------------------------
% 0.22/0.52  % (19586)Refutation not found, incomplete strategy% (19586)------------------------------
% 0.22/0.52  % (19586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19586)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19586)Memory used [KB]: 1663
% 0.22/0.52  % (19586)Time elapsed: 0.108 s
% 0.22/0.52  % (19586)------------------------------
% 0.22/0.52  % (19586)------------------------------
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f265,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f264,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f264,plain,(
% 0.22/0.52    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.22/0.52    inference(forward_demodulation,[],[f260,f236])).
% 0.22/0.52  fof(f236,plain,(
% 0.22/0.52    k1_xboole_0 = sK2),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f228])).
% 0.22/0.52  fof(f228,plain,(
% 0.22/0.52    sK2 != sK2 | k1_xboole_0 = sK2),
% 0.22/0.52    inference(superposition,[],[f194,f151])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    sK2 = k1_tarski(sK0) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(resolution,[],[f145,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    r1_tarski(sK2,k1_tarski(sK0))),
% 0.22/0.52    inference(superposition,[],[f127,f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.52    inference(negated_conjecture,[],[f10])).
% 0.22/0.52  fof(f10,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    ( ! [X4,X5] : (r1_tarski(X4,k2_xboole_0(X5,X4))) )),
% 0.22/0.52    inference(superposition,[],[f25,f86])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 0.22/0.52    inference(superposition,[],[f43,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 0.22/0.52    inference(superposition,[],[f27,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.52  fof(f194,plain,(
% 0.22/0.52    sK2 != k1_tarski(sK0)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f177])).
% 0.22/0.52  fof(f177,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | sK2 != k1_tarski(sK0)),
% 0.22/0.52    inference(backward_demodulation,[],[f22,f174])).
% 0.22/0.52  fof(f174,plain,(
% 0.22/0.52    k1_xboole_0 = sK1),
% 0.22/0.52    inference(subsumption_resolution,[],[f173,f79])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    sK1 != sK1 | k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 0.22/0.52    inference(superposition,[],[f23,f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 0.22/0.52    inference(resolution,[],[f33,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    r1_tarski(sK1,k1_tarski(sK0))),
% 0.22/0.52    inference(superposition,[],[f25,f20])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f173,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 0.22/0.52    inference(subsumption_resolution,[],[f172,f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | sK1 != sK2),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    sK1 != sK2 | sK1 != sK1 | k1_xboole_0 = sK1),
% 0.22/0.52    inference(superposition,[],[f21,f68])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | sK1 = sK2),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f168])).
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | sK1 = sK2 | k1_xboole_0 = sK1),
% 0.22/0.52    inference(resolution,[],[f153,f77])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_xboole_0 = X0 | sK1 = X0 | k1_xboole_0 = sK1) )),
% 0.22/0.52    inference(superposition,[],[f33,f68])).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    r1_tarski(sK2,sK1) | k1_xboole_0 = sK1),
% 0.22/0.52    inference(superposition,[],[f145,f68])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f260,plain,(
% 0.22/0.52    ~r1_tarski(k1_xboole_0,sK2)),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f241])).
% 0.22/0.52  fof(f241,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k1_xboole_0,sK2)),
% 0.22/0.52    inference(backward_demodulation,[],[f104,f236])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    ~r1_tarski(k1_xboole_0,sK2) | k1_xboole_0 != sK2),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f99])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    ~r1_tarski(k1_xboole_0,sK2) | k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != sK2),
% 0.22/0.52    inference(superposition,[],[f59,f79])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ~r1_tarski(sK1,sK2) | k1_xboole_0 != sK1),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    sK2 != sK2 | k1_xboole_0 != sK1 | ~r1_tarski(sK1,sK2)),
% 0.22/0.52    inference(superposition,[],[f22,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    sK2 = k1_tarski(sK0) | ~r1_tarski(sK1,sK2)),
% 0.22/0.52    inference(superposition,[],[f29,f20])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (19590)------------------------------
% 0.22/0.52  % (19590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19590)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (19590)Memory used [KB]: 1791
% 0.22/0.52  % (19590)Time elapsed: 0.102 s
% 0.22/0.52  % (19590)------------------------------
% 0.22/0.52  % (19590)------------------------------
% 0.22/0.52  % (19580)Success in time 0.161 s
%------------------------------------------------------------------------------
