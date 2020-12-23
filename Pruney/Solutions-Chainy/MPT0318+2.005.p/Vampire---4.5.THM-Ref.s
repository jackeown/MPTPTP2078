%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:16 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   36 (  71 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 187 expanded)
%              Number of equality atoms :   75 ( 156 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f25,f53,f60,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f60,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f59,f25])).

fof(f59,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f58,f53])).

fof(f58,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(trivial_inequality_removal,[],[f55])).

fof(f55,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(superposition,[],[f35,f26])).

fof(f26,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
      | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
          | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
        & k1_xboole_0 != X0 )
   => ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f53,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f49,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f51,f27])).

fof(f27,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f30,f50])).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f31,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f25,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.10  % Command    : run_vampire %s %d
% 0.10/0.30  % Computer   : n002.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 16:14:51 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.15/0.42  % (12128)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.15/0.43  % (12144)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.15/0.44  % (12144)Refutation not found, incomplete strategy% (12144)------------------------------
% 0.15/0.44  % (12144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.44  % (12144)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.44  
% 0.15/0.44  % (12144)Memory used [KB]: 10746
% 0.15/0.44  % (12144)Time elapsed: 0.070 s
% 0.15/0.44  % (12144)------------------------------
% 0.15/0.44  % (12144)------------------------------
% 0.15/0.46  % (12125)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.15/0.46  % (12124)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.15/0.46  % (12125)Refutation not found, incomplete strategy% (12125)------------------------------
% 0.15/0.46  % (12125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.46  % (12125)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.46  
% 0.15/0.46  % (12125)Memory used [KB]: 1663
% 0.15/0.46  % (12125)Time elapsed: 0.099 s
% 0.15/0.46  % (12125)------------------------------
% 0.15/0.46  % (12125)------------------------------
% 0.15/0.47  % (12127)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.15/0.47  % (12122)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.15/0.47  % (12127)Refutation found. Thanks to Tanya!
% 0.15/0.47  % SZS status Theorem for theBenchmark
% 0.15/0.47  % SZS output start Proof for theBenchmark
% 0.15/0.47  fof(f61,plain,(
% 0.15/0.47    $false),
% 0.15/0.47    inference(unit_resulting_resolution,[],[f25,f53,f60,f35])).
% 0.15/0.47  fof(f35,plain,(
% 0.15/0.47    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.15/0.47    inference(cnf_transformation,[],[f23])).
% 0.15/0.47  fof(f23,plain,(
% 0.15/0.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.15/0.47    inference(flattening,[],[f22])).
% 0.15/0.47  fof(f22,plain,(
% 0.15/0.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.15/0.47    inference(nnf_transformation,[],[f12])).
% 0.15/0.47  fof(f12,axiom,(
% 0.15/0.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.15/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.15/0.47  fof(f60,plain,(
% 0.15/0.47    k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.15/0.47    inference(subsumption_resolution,[],[f59,f25])).
% 0.15/0.47  fof(f59,plain,(
% 0.15/0.47    k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.15/0.47    inference(subsumption_resolution,[],[f58,f53])).
% 0.15/0.47  fof(f58,plain,(
% 0.15/0.47    k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.15/0.47    inference(trivial_inequality_removal,[],[f55])).
% 0.15/0.47  fof(f55,plain,(
% 0.15/0.47    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.15/0.47    inference(superposition,[],[f35,f26])).
% 0.15/0.47  fof(f26,plain,(
% 0.15/0.47    k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.15/0.47    inference(cnf_transformation,[],[f19])).
% 0.15/0.47  fof(f19,plain,(
% 0.15/0.47    (k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0),
% 0.15/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).
% 0.15/0.47  fof(f18,plain,(
% 0.15/0.47    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0) => ((k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0)),
% 0.15/0.47    introduced(choice_axiom,[])).
% 0.15/0.47  fof(f16,plain,(
% 0.15/0.47    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.15/0.47    inference(ennf_transformation,[],[f15])).
% 0.15/0.47  fof(f15,negated_conjecture,(
% 0.15/0.47    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.15/0.47    inference(negated_conjecture,[],[f14])).
% 0.15/0.47  fof(f14,conjecture,(
% 0.15/0.47    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.15/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.15/0.47  fof(f53,plain,(
% 0.15/0.47    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 0.15/0.47    inference(backward_demodulation,[],[f49,f52])).
% 0.15/0.47  fof(f52,plain,(
% 0.15/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.15/0.47    inference(forward_demodulation,[],[f51,f27])).
% 0.15/0.47  fof(f27,plain,(
% 0.15/0.47    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.15/0.47    inference(cnf_transformation,[],[f4])).
% 0.15/0.47  fof(f4,axiom,(
% 0.15/0.47    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.15/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.15/0.47  fof(f51,plain,(
% 0.15/0.47    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 0.15/0.47    inference(superposition,[],[f30,f50])).
% 0.15/0.47  fof(f50,plain,(
% 0.15/0.47    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.15/0.47    inference(resolution,[],[f31,f45])).
% 0.15/0.47  fof(f45,plain,(
% 0.15/0.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.15/0.47    inference(equality_resolution,[],[f33])).
% 0.15/0.47  fof(f33,plain,(
% 0.15/0.47    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.15/0.47    inference(cnf_transformation,[],[f21])).
% 0.15/0.47  fof(f21,plain,(
% 0.15/0.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.15/0.47    inference(flattening,[],[f20])).
% 0.15/0.47  fof(f20,plain,(
% 0.15/0.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.15/0.47    inference(nnf_transformation,[],[f1])).
% 0.15/0.47  fof(f1,axiom,(
% 0.15/0.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.15/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.15/0.47  fof(f31,plain,(
% 0.15/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.15/0.47    inference(cnf_transformation,[],[f17])).
% 0.15/0.47  fof(f17,plain,(
% 0.15/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.15/0.47    inference(ennf_transformation,[],[f3])).
% 0.15/0.47  fof(f3,axiom,(
% 0.15/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.15/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.15/0.47  fof(f30,plain,(
% 0.15/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.15/0.47    inference(cnf_transformation,[],[f2])).
% 0.15/0.47  fof(f2,axiom,(
% 0.15/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.15/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.15/0.47  fof(f49,plain,(
% 0.15/0.47    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.15/0.47    inference(equality_resolution,[],[f38])).
% 0.15/0.47  fof(f38,plain,(
% 0.15/0.47    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.15/0.47    inference(cnf_transformation,[],[f24])).
% 0.15/0.47  fof(f24,plain,(
% 0.15/0.47    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.15/0.47    inference(nnf_transformation,[],[f13])).
% 0.15/0.47  fof(f13,axiom,(
% 0.15/0.47    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.15/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.15/0.47  fof(f25,plain,(
% 0.15/0.47    k1_xboole_0 != sK0),
% 0.15/0.47    inference(cnf_transformation,[],[f19])).
% 0.15/0.47  % SZS output end Proof for theBenchmark
% 0.15/0.47  % (12127)------------------------------
% 0.15/0.47  % (12127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.47  % (12127)Termination reason: Refutation
% 0.15/0.47  
% 0.15/0.47  % (12127)Memory used [KB]: 1791
% 0.15/0.47  % (12127)Time elapsed: 0.108 s
% 0.15/0.47  % (12127)------------------------------
% 0.15/0.47  % (12127)------------------------------
% 0.15/0.47  % (12119)Success in time 0.158 s
%------------------------------------------------------------------------------
