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
% DateTime   : Thu Dec  3 12:42:12 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   33 (  51 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :   12
%              Number of atoms          :   70 ( 118 expanded)
%              Number of equality atoms :   25 (  34 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112,plain,(
    $false ),
    inference(subsumption_resolution,[],[f111,f58])).

fof(f58,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f33,f48])).

fof(f48,plain,(
    ! [X2,X3] : r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X3,X1] :
      ( X1 != X3
      | r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X2
      | X1 != X3
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f111,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f110,f64])).

fof(f64,plain,(
    r2_hidden(sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,sK3) ),
    inference(resolution,[],[f34,f18])).

fof(f18,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))
    | r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <~> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      <=> ( r2_hidden(X1,X3)
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f110,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(resolution,[],[f35,f85])).

fof(f85,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3)) ),
    inference(subsumption_resolution,[],[f84,f64])).

fof(f84,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3)) ),
    inference(trivial_inequality_removal,[],[f82])).

fof(f82,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3)) ),
    inference(backward_demodulation,[],[f49,f80])).

fof(f80,plain,(
    sK0 = sK2 ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,
    ( sK0 = sK2
    | sK0 = sK2 ),
    inference(resolution,[],[f74,f57])).

fof(f57,plain,
    ( r2_hidden(sK0,k1_tarski(sK2))
    | sK0 = sK2 ),
    inference(resolution,[],[f33,f17])).

fof(f17,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))
    | sK0 = sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X2))
      | X1 = X2 ) ),
    inference(trivial_inequality_removal,[],[f73])).

fof(f73,plain,(
    ! [X2,X1] :
      ( k1_tarski(X1) != k1_tarski(X1)
      | ~ r2_hidden(X1,k1_tarski(X2))
      | X1 = X2 ) ),
    inference(superposition,[],[f25,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f49,plain,
    ( sK0 != sK2
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3)) ),
    inference(inner_rewriting,[],[f16])).

fof(f16,plain,
    ( sK0 != sK2
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:27:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.48  % (27878)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.49  % (27878)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % (27886)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f112,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(subsumption_resolution,[],[f111,f58])).
% 0.19/0.49  fof(f58,plain,(
% 0.19/0.49    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.19/0.49    inference(resolution,[],[f33,f48])).
% 0.19/0.49  fof(f48,plain,(
% 0.19/0.49    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 0.19/0.49    inference(equality_resolution,[],[f47])).
% 0.19/0.49  fof(f47,plain,(
% 0.19/0.49    ( ! [X2,X3,X1] : (X1 != X3 | r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 0.19/0.49    inference(equality_resolution,[],[f41])).
% 0.19/0.49  fof(f41,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (X0 != X2 | X1 != X3 | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,axiom,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 0.19/0.49  fof(f33,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.19/0.49  fof(f111,plain,(
% 0.19/0.49    ~r2_hidden(sK0,k1_tarski(sK0))),
% 0.19/0.49    inference(subsumption_resolution,[],[f110,f64])).
% 0.19/0.49  fof(f64,plain,(
% 0.19/0.49    r2_hidden(sK1,sK3)),
% 0.19/0.49    inference(duplicate_literal_removal,[],[f60])).
% 0.19/0.49  fof(f60,plain,(
% 0.19/0.49    r2_hidden(sK1,sK3) | r2_hidden(sK1,sK3)),
% 0.19/0.49    inference(resolution,[],[f34,f18])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) | r2_hidden(sK1,sK3)),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f13,plain,(
% 0.19/0.49    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <~> (r2_hidden(X1,X3) & X0 = X2))),
% 0.19/0.49    inference(ennf_transformation,[],[f12])).
% 0.19/0.49  fof(f12,negated_conjecture,(
% 0.19/0.49    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 0.19/0.49    inference(negated_conjecture,[],[f11])).
% 0.19/0.49  fof(f11,conjecture,(
% 0.19/0.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 0.19/0.49  fof(f34,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f5])).
% 0.19/0.49  fof(f110,plain,(
% 0.19/0.49    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK0,k1_tarski(sK0))),
% 0.19/0.49    inference(resolution,[],[f35,f85])).
% 0.19/0.49  fof(f85,plain,(
% 0.19/0.49    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3))),
% 0.19/0.49    inference(subsumption_resolution,[],[f84,f64])).
% 0.19/0.49  fof(f84,plain,(
% 0.19/0.49    ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3))),
% 0.19/0.49    inference(trivial_inequality_removal,[],[f82])).
% 0.19/0.49  fof(f82,plain,(
% 0.19/0.49    sK0 != sK0 | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3))),
% 0.19/0.49    inference(backward_demodulation,[],[f49,f80])).
% 0.19/0.49  fof(f80,plain,(
% 0.19/0.49    sK0 = sK2),
% 0.19/0.49    inference(duplicate_literal_removal,[],[f77])).
% 0.19/0.49  fof(f77,plain,(
% 0.19/0.49    sK0 = sK2 | sK0 = sK2),
% 0.19/0.49    inference(resolution,[],[f74,f57])).
% 0.19/0.49  fof(f57,plain,(
% 0.19/0.49    r2_hidden(sK0,k1_tarski(sK2)) | sK0 = sK2),
% 0.19/0.49    inference(resolution,[],[f33,f17])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) | sK0 = sK2),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f74,plain,(
% 0.19/0.49    ( ! [X2,X1] : (~r2_hidden(X1,k1_tarski(X2)) | X1 = X2) )),
% 0.19/0.49    inference(trivial_inequality_removal,[],[f73])).
% 0.19/0.49  fof(f73,plain,(
% 0.19/0.49    ( ! [X2,X1] : (k1_tarski(X1) != k1_tarski(X1) | ~r2_hidden(X1,k1_tarski(X2)) | X1 = X2) )),
% 0.19/0.49    inference(superposition,[],[f25,f26])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.19/0.49    inference(cnf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,axiom,(
% 0.19/0.49    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.19/0.49  fof(f49,plain,(
% 0.19/0.49    sK0 != sK2 | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3))),
% 0.19/0.49    inference(inner_rewriting,[],[f16])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    sK0 != sK2 | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f35,plain,(
% 0.19/0.49    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f5])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (27878)------------------------------
% 0.19/0.49  % (27878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (27878)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (27878)Memory used [KB]: 6268
% 0.19/0.49  % (27878)Time elapsed: 0.100 s
% 0.19/0.49  % (27878)------------------------------
% 0.19/0.49  % (27878)------------------------------
% 0.19/0.49  % (27871)Success in time 0.142 s
%------------------------------------------------------------------------------
