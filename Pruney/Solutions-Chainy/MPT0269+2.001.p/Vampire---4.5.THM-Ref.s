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
% DateTime   : Thu Dec  3 12:40:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  65 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :   13
%              Number of atoms          :   85 ( 185 expanded)
%              Number of equality atoms :   45 ( 129 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,plain,(
    $false ),
    inference(subsumption_resolution,[],[f54,f46])).

fof(f46,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK0) ),
    inference(resolution,[],[f44,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f44,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f39,f22])).

fof(f22,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK0 != k1_tarski(sK1)
    & k1_xboole_0 != sK0
    & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).

% (22294)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f14,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( sK0 != k1_tarski(sK1)
      & k1_xboole_0 != sK0
      & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f39,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK1,sK0) ),
    inference(superposition,[],[f21,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f21,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK1),sK0) ),
    inference(resolution,[],[f53,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f53,plain,(
    ~ r1_tarski(k1_tarski(sK1),sK0) ),
    inference(subsumption_resolution,[],[f52,f23])).

fof(f23,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,
    ( sK0 = k1_tarski(sK1)
    | ~ r1_tarski(k1_tarski(sK1),sK0) ),
    inference(resolution,[],[f50,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f50,plain,(
    ~ r2_xboole_0(k1_tarski(sK1),sK0) ),
    inference(resolution,[],[f49,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f49,plain,(
    r2_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f48,f23])).

fof(f48,plain,
    ( r2_xboole_0(sK0,k1_tarski(sK1))
    | sK0 = k1_tarski(sK1) ),
    inference(resolution,[],[f43,f29])).

fof(f43,plain,(
    r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(trivial_inequality_removal,[],[f42])).

fof(f42,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(superposition,[],[f30,f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:42:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.53  % (22279)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (22289)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (22272)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (22282)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (22289)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f54,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK0)),
% 0.21/0.55    inference(resolution,[],[f44,f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.21/0.55    inference(nnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    r2_hidden(sK1,sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f39,f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    k1_xboole_0 != sK0),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).
% 0.21/0.55  % (22294)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1))) => (sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.21/0.55    inference(negated_conjecture,[],[f10])).
% 0.21/0.55  fof(f10,conjecture,(
% 0.21/0.55    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    k1_xboole_0 = sK0 | r2_hidden(sK1,sK0)),
% 0.21/0.55    inference(superposition,[],[f21,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    k1_xboole_0 != k4_xboole_0(k1_tarski(sK1),sK0)),
% 0.21/0.55    inference(resolution,[],[f53,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.55    inference(nnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ~r1_tarski(k1_tarski(sK1),sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f52,f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    sK0 != k1_tarski(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    sK0 = k1_tarski(sK1) | ~r1_tarski(k1_tarski(sK1),sK0)),
% 0.21/0.55    inference(resolution,[],[f50,f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.55    inference(flattening,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.55    inference(nnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ~r2_xboole_0(k1_tarski(sK1),sK0)),
% 0.21/0.55    inference(resolution,[],[f49,f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    r2_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.55    inference(subsumption_resolution,[],[f48,f23])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    r2_xboole_0(sK0,k1_tarski(sK1)) | sK0 = k1_tarski(sK1)),
% 0.21/0.55    inference(resolution,[],[f43,f29])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    r1_tarski(sK0,k1_tarski(sK1))),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k1_tarski(sK1))),
% 0.21/0.55    inference(superposition,[],[f30,f21])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (22289)------------------------------
% 0.21/0.55  % (22289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22289)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (22289)Memory used [KB]: 1663
% 0.21/0.55  % (22289)Time elapsed: 0.099 s
% 0.21/0.55  % (22289)------------------------------
% 0.21/0.55  % (22289)------------------------------
% 0.21/0.56  % (22257)Success in time 0.194 s
%------------------------------------------------------------------------------
