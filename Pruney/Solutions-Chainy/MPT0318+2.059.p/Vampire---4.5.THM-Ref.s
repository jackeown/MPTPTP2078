%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  54 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :   12
%              Number of atoms          :   71 ( 141 expanded)
%              Number of equality atoms :   70 ( 140 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f42,plain,(
    $false ),
    inference(subsumption_resolution,[],[f41,f30])).

% (15622)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (15623)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (15614)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (15613)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (15619)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (15627)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (15622)Refutation not found, incomplete strategy% (15622)------------------------------
% (15622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15622)Termination reason: Refutation not found, incomplete strategy

% (15622)Memory used [KB]: 10618
% (15622)Time elapsed: 0.061 s
% (15622)------------------------------
% (15622)------------------------------
fof(f30,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f28,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(superposition,[],[f18,f17])).

fof(f17,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f18,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

fof(f28,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f41,plain,(
    k1_xboole_0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f40,f15])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
      | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f40,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(trivial_inequality_removal,[],[f39])).

fof(f39,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k1_tarski(sK1) ),
    inference(superposition,[],[f20,f38])).

fof(f38,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f37,f15])).

fof(f37,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f36,f30])).

fof(f36,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(trivial_inequality_removal,[],[f35])).

fof(f35,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(superposition,[],[f20,f16])).

fof(f16,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (15620)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.47  % (15605)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.48  % (15611)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.48  % (15628)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.49  % (15620)Refutation not found, incomplete strategy% (15620)------------------------------
% 0.21/0.49  % (15620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15620)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (15620)Memory used [KB]: 6140
% 0.21/0.49  % (15620)Time elapsed: 0.086 s
% 0.21/0.49  % (15620)------------------------------
% 0.21/0.49  % (15620)------------------------------
% 0.21/0.49  % (15612)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.49  % (15610)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.49  % (15612)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (15605)Refutation not found, incomplete strategy% (15605)------------------------------
% 0.21/0.49  % (15605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15605)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (15605)Memory used [KB]: 1663
% 0.21/0.49  % (15605)Time elapsed: 0.095 s
% 0.21/0.49  % (15605)------------------------------
% 0.21/0.49  % (15605)------------------------------
% 0.21/0.49  % (15607)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (15631)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f41,f30])).
% 0.21/0.49  % (15622)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.49  % (15623)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.50  % (15614)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (15613)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (15619)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (15627)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (15622)Refutation not found, incomplete strategy% (15622)------------------------------
% 0.21/0.50  % (15622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (15622)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (15622)Memory used [KB]: 10618
% 0.21/0.50  % (15622)Time elapsed: 0.061 s
% 0.21/0.50  % (15622)------------------------------
% 0.21/0.50  % (15622)------------------------------
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f28,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 0.21/0.50    inference(superposition,[],[f18,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    k1_xboole_0 = k1_tarski(sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f40,f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    k1_xboole_0 != sK0),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    (k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0) => ((k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0)),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.21/0.50    inference(negated_conjecture,[],[f7])).
% 0.21/0.50  fof(f7,conjecture,(
% 0.21/0.50    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = k1_tarski(sK1)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k1_tarski(sK1)),
% 0.21/0.50    inference(superposition,[],[f20,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f37,f15])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f36,f30])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.21/0.50    inference(superposition,[],[f20,f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.50    inference(nnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (15612)------------------------------
% 0.21/0.50  % (15612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (15612)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (15612)Memory used [KB]: 6140
% 0.21/0.50  % (15612)Time elapsed: 0.086 s
% 0.21/0.50  % (15612)------------------------------
% 0.21/0.50  % (15612)------------------------------
% 0.21/0.50  % (15604)Success in time 0.145 s
%------------------------------------------------------------------------------
