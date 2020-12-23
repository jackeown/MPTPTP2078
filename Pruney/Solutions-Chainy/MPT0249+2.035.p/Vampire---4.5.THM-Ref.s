%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:15 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   36 (  64 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :   12
%              Number of atoms          :   97 ( 227 expanded)
%              Number of equality atoms :   57 ( 176 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(subsumption_resolution,[],[f72,f22])).

fof(f22,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f72,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f70,f20])).

fof(f20,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f70,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f54,f37])).

fof(f37,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f54,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | sK1 = X0
      | k1_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f40,f50])).

fof(f50,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f48,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f43,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f43,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f39,f34])).

fof(f34,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_tarski(sK0),X1)
      | r1_tarski(sK1,X1) ) ),
    inference(superposition,[],[f30,f19])).

fof(f19,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f40,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | k1_xboole_0 = X0
      | k1_tarski(sK0) = X0 ) ),
    inference(resolution,[],[f38,f23])).

fof(f38,plain,(
    ! [X0] :
      ( r1_tarski(X0,k1_tarski(sK0))
      | ~ r1_tarski(X0,sK2) ) ),
    inference(superposition,[],[f31,f19])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n003.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 11:44:42 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.45  % (29749)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.18/0.45  % (29740)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.18/0.45  % (29740)Refutation found. Thanks to Tanya!
% 0.18/0.45  % SZS status Theorem for theBenchmark
% 0.18/0.45  % SZS output start Proof for theBenchmark
% 0.18/0.45  fof(f73,plain,(
% 0.18/0.45    $false),
% 0.18/0.45    inference(subsumption_resolution,[],[f72,f22])).
% 0.18/0.45  fof(f22,plain,(
% 0.18/0.45    k1_xboole_0 != sK2),
% 0.18/0.45    inference(cnf_transformation,[],[f14])).
% 0.18/0.45  fof(f14,plain,(
% 0.18/0.45    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.18/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).
% 0.18/0.45  fof(f13,plain,(
% 0.18/0.45    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 0.18/0.45    introduced(choice_axiom,[])).
% 0.18/0.45  fof(f10,plain,(
% 0.18/0.45    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.18/0.45    inference(ennf_transformation,[],[f9])).
% 0.18/0.45  fof(f9,negated_conjecture,(
% 0.18/0.45    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.18/0.45    inference(negated_conjecture,[],[f8])).
% 0.18/0.45  fof(f8,conjecture,(
% 0.18/0.45    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.18/0.45  fof(f72,plain,(
% 0.18/0.45    k1_xboole_0 = sK2),
% 0.18/0.45    inference(subsumption_resolution,[],[f70,f20])).
% 0.18/0.45  fof(f20,plain,(
% 0.18/0.45    sK1 != sK2),
% 0.18/0.45    inference(cnf_transformation,[],[f14])).
% 0.18/0.45  fof(f70,plain,(
% 0.18/0.45    sK1 = sK2 | k1_xboole_0 = sK2),
% 0.18/0.45    inference(resolution,[],[f54,f37])).
% 0.18/0.45  fof(f37,plain,(
% 0.18/0.45    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.18/0.45    inference(equality_resolution,[],[f26])).
% 0.18/0.45  fof(f26,plain,(
% 0.18/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.18/0.45    inference(cnf_transformation,[],[f18])).
% 0.18/0.45  fof(f18,plain,(
% 0.18/0.45    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.18/0.45    inference(flattening,[],[f17])).
% 0.18/0.45  fof(f17,plain,(
% 0.18/0.45    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.18/0.45    inference(nnf_transformation,[],[f1])).
% 0.18/0.45  fof(f1,axiom,(
% 0.18/0.45    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.18/0.45  fof(f54,plain,(
% 0.18/0.45    ( ! [X0] : (~r1_tarski(X0,sK2) | sK1 = X0 | k1_xboole_0 = X0) )),
% 0.18/0.45    inference(backward_demodulation,[],[f40,f50])).
% 0.18/0.45  fof(f50,plain,(
% 0.18/0.45    sK1 = k1_tarski(sK0)),
% 0.18/0.45    inference(subsumption_resolution,[],[f48,f21])).
% 0.18/0.45  fof(f21,plain,(
% 0.18/0.45    k1_xboole_0 != sK1),
% 0.18/0.45    inference(cnf_transformation,[],[f14])).
% 0.18/0.45  fof(f48,plain,(
% 0.18/0.45    k1_xboole_0 = sK1 | sK1 = k1_tarski(sK0)),
% 0.18/0.45    inference(resolution,[],[f43,f23])).
% 0.18/0.45  fof(f23,plain,(
% 0.18/0.45    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.18/0.45    inference(cnf_transformation,[],[f16])).
% 0.18/0.45  fof(f16,plain,(
% 0.18/0.45    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.18/0.45    inference(flattening,[],[f15])).
% 0.18/0.45  fof(f15,plain,(
% 0.18/0.45    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.18/0.45    inference(nnf_transformation,[],[f6])).
% 0.18/0.45  fof(f6,axiom,(
% 0.18/0.45    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.18/0.45  fof(f43,plain,(
% 0.18/0.45    r1_tarski(sK1,k1_tarski(sK0))),
% 0.18/0.45    inference(resolution,[],[f39,f34])).
% 0.18/0.45  fof(f34,plain,(
% 0.18/0.45    ( ! [X1] : (r1_tarski(k1_tarski(X1),k1_tarski(X1))) )),
% 0.18/0.45    inference(equality_resolution,[],[f25])).
% 0.18/0.45  fof(f25,plain,(
% 0.18/0.45    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) != X0) )),
% 0.18/0.45    inference(cnf_transformation,[],[f16])).
% 0.18/0.45  fof(f39,plain,(
% 0.18/0.45    ( ! [X1] : (~r1_tarski(k1_tarski(sK0),X1) | r1_tarski(sK1,X1)) )),
% 0.18/0.45    inference(superposition,[],[f30,f19])).
% 0.18/0.45  fof(f19,plain,(
% 0.18/0.45    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.18/0.45    inference(cnf_transformation,[],[f14])).
% 0.18/0.45  fof(f30,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f11])).
% 0.18/0.45  fof(f11,plain,(
% 0.18/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.18/0.45    inference(ennf_transformation,[],[f3])).
% 0.18/0.45  fof(f3,axiom,(
% 0.18/0.45    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.18/0.45  fof(f40,plain,(
% 0.18/0.45    ( ! [X0] : (~r1_tarski(X0,sK2) | k1_xboole_0 = X0 | k1_tarski(sK0) = X0) )),
% 0.18/0.45    inference(resolution,[],[f38,f23])).
% 0.18/0.45  fof(f38,plain,(
% 0.18/0.45    ( ! [X0] : (r1_tarski(X0,k1_tarski(sK0)) | ~r1_tarski(X0,sK2)) )),
% 0.18/0.45    inference(superposition,[],[f31,f19])).
% 0.18/0.45  fof(f31,plain,(
% 0.18/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.18/0.45    inference(cnf_transformation,[],[f12])).
% 0.18/0.45  fof(f12,plain,(
% 0.18/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.18/0.45    inference(ennf_transformation,[],[f2])).
% 0.18/0.45  fof(f2,axiom,(
% 0.18/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.18/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.18/0.45  % SZS output end Proof for theBenchmark
% 0.18/0.45  % (29740)------------------------------
% 0.18/0.45  % (29740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.45  % (29740)Termination reason: Refutation
% 0.18/0.45  
% 0.18/0.45  % (29740)Memory used [KB]: 1663
% 0.18/0.45  % (29740)Time elapsed: 0.044 s
% 0.18/0.45  % (29740)------------------------------
% 0.18/0.45  % (29740)------------------------------
% 0.18/0.46  % (29733)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.18/0.46  % (29723)Success in time 0.114 s
%------------------------------------------------------------------------------
