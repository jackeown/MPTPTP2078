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
% DateTime   : Thu Dec  3 12:42:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  82 expanded)
%              Number of leaves         :    7 (  20 expanded)
%              Depth                    :   14
%              Number of atoms          :   83 ( 251 expanded)
%              Number of equality atoms :   71 ( 239 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(subsumption_resolution,[],[f57,f56])).

fof(f56,plain,(
    ! [X0] : ~ r2_hidden(sK1,X0) ),
    inference(subsumption_resolution,[],[f54,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

% (13738)Refutation not found, incomplete strategy% (13738)------------------------------
% (13738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13738)Termination reason: Refutation not found, incomplete strategy

% (13738)Memory used [KB]: 1663
% (13738)Time elapsed: 0.060 s
% (13738)------------------------------
% (13738)------------------------------
fof(f54,plain,(
    ! [X0] :
      ( k4_xboole_0(X0,k1_xboole_0) != X0
      | ~ r2_hidden(sK1,X0) ) ),
    inference(superposition,[],[f24,f51])).

fof(f51,plain,(
    k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f50,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
      | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
          | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
        & k1_xboole_0 != X0 )
   => ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f50,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(trivial_inequality_removal,[],[f49])).

fof(f49,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k1_tarski(sK1)
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(superposition,[],[f21,f33])).

fof(f33,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f32,f16])).

fof(f32,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(trivial_inequality_removal,[],[f31])).

fof(f31,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(superposition,[],[f21,f17])).

fof(f17,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
     => ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f57,plain,(
    ! [X1] : r2_hidden(sK1,X1) ),
    inference(subsumption_resolution,[],[f55,f18])).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f55,plain,(
    ! [X1] :
      ( k1_xboole_0 != k3_xboole_0(X1,k1_xboole_0)
      | r2_hidden(sK1,X1) ) ),
    inference(superposition,[],[f20,f51])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:47:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.46  % (13740)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.46  % (13738)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (13731)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (13740)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (13732)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f57,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(sK1,X0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f54,f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.47  % (13738)Refutation not found, incomplete strategy% (13738)------------------------------
% 0.20/0.47  % (13738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (13738)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (13738)Memory used [KB]: 1663
% 0.20/0.47  % (13738)Time elapsed: 0.060 s
% 0.20/0.47  % (13738)------------------------------
% 0.20/0.47  % (13738)------------------------------
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) != X0 | ~r2_hidden(sK1,X0)) )),
% 0.20/0.47    inference(superposition,[],[f24,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    k1_xboole_0 = k1_tarski(sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f50,f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    k1_xboole_0 != sK0),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    (k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0) => ((k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0)),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.20/0.47    inference(negated_conjecture,[],[f6])).
% 0.20/0.47  fof(f6,conjecture,(
% 0.20/0.47    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    k1_xboole_0 = sK0 | k1_xboole_0 = k1_tarski(sK1)),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f49])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k1_tarski(sK1)),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = k1_tarski(sK1)),
% 0.20/0.47    inference(superposition,[],[f21,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k1_tarski(sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f32,f16])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.20/0.47    inference(superposition,[],[f21,f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.47    inference(flattening,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0)),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 => ~r2_hidden(X1,X0))),
% 0.20/0.47    inference(unused_predicate_definition_removal,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X1] : (r2_hidden(sK1,X1)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f55,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X1] : (k1_xboole_0 != k3_xboole_0(X1,k1_xboole_0) | r2_hidden(sK1,X1)) )),
% 0.20/0.47    inference(superposition,[],[f20,f51])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) | r2_hidden(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (13740)------------------------------
% 0.20/0.47  % (13740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (13740)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (13740)Memory used [KB]: 6140
% 0.20/0.47  % (13740)Time elapsed: 0.008 s
% 0.20/0.47  % (13740)------------------------------
% 0.20/0.47  % (13740)------------------------------
% 0.20/0.47  % (13724)Success in time 0.116 s
%------------------------------------------------------------------------------
