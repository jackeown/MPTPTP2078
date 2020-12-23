%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 211 expanded)
%              Number of leaves         :   11 (  56 expanded)
%              Depth                    :   20
%              Number of atoms          :  161 ( 684 expanded)
%              Number of equality atoms :   87 ( 378 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f381,plain,(
    $false ),
    inference(subsumption_resolution,[],[f360,f375])).

fof(f375,plain,(
    ! [X4,X1] : X1 = X4 ),
    inference(subsumption_resolution,[],[f373,f303])).

fof(f303,plain,(
    ! [X4] : r2_hidden(X4,sK0) ),
    inference(backward_demodulation,[],[f49,f288])).

fof(f288,plain,(
    ! [X10] : sK0 = X10 ),
    inference(condensation,[],[f285])).

fof(f285,plain,(
    ! [X10,X9] :
      ( sK0 = X9
      | sK0 = X10 ) ),
    inference(resolution,[],[f264,f52])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
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

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f264,plain,(
    ! [X0] : r2_hidden(sK0,X0) ),
    inference(subsumption_resolution,[],[f248,f30])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f248,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | r2_hidden(sK0,X0) ) ),
    inference(superposition,[],[f45,f184])).

fof(f184,plain,(
    k1_xboole_0 = k2_tarski(sK0,sK1) ),
    inference(resolution,[],[f97,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f38,f29])).

fof(f29,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f97,plain,(
    v1_xboole_0(k2_tarski(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f96,f29])).

fof(f96,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k2_tarski(sK0,sK1)) ),
    inference(superposition,[],[f37,f82])).

fof(f82,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k2_tarski(sK0,sK1)) ),
    inference(backward_demodulation,[],[f59,f79])).

fof(f79,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f68,f29])).

fof(f68,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | sK2 = X1 ) ),
    inference(resolution,[],[f38,f58])).

fof(f58,plain,(
    v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f56,f29])).

fof(f56,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK2) ),
    inference(superposition,[],[f37,f28])).

fof(f28,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

% (3130)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f59,plain,(
    k1_xboole_0 = k2_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    inference(superposition,[],[f34,f28])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f49,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

% (3130)Refutation not found, incomplete strategy% (3130)------------------------------
% (3130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3130)Termination reason: Refutation not found, incomplete strategy

% (3130)Memory used [KB]: 6140
% (3130)Time elapsed: 0.138 s
% (3130)------------------------------
% (3130)------------------------------
fof(f373,plain,(
    ! [X4,X1] :
      ( ~ r2_hidden(X4,sK0)
      | X1 = X4 ) ),
    inference(condensation,[],[f305])).

fof(f305,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,sK0)
      | X0 = X4
      | X1 = X4 ) ),
    inference(backward_demodulation,[],[f52,f288])).

fof(f360,plain,(
    ! [X1] : k1_xboole_0 != k2_xboole_0(sK0,X1) ),
    inference(backward_demodulation,[],[f33,f288])).

fof(f33,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:00:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (3125)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (3117)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (3109)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (3115)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (3113)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (3114)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (3103)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (3103)Refutation not found, incomplete strategy% (3103)------------------------------
% 0.21/0.53  % (3103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3103)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3103)Memory used [KB]: 1663
% 0.21/0.53  % (3103)Time elapsed: 0.115 s
% 0.21/0.53  % (3103)------------------------------
% 0.21/0.53  % (3103)------------------------------
% 0.21/0.53  % (3102)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (3129)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (3105)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (3108)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (3107)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (3109)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (3106)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f381,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f360,f375])).
% 0.21/0.54  fof(f375,plain,(
% 0.21/0.54    ( ! [X4,X1] : (X1 = X4) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f373,f303])).
% 0.21/0.54  fof(f303,plain,(
% 0.21/0.54    ( ! [X4] : (r2_hidden(X4,sK0)) )),
% 0.21/0.54    inference(backward_demodulation,[],[f49,f288])).
% 0.21/0.54  fof(f288,plain,(
% 0.21/0.54    ( ! [X10] : (sK0 = X10) )),
% 0.21/0.54    inference(condensation,[],[f285])).
% 0.21/0.54  fof(f285,plain,(
% 0.21/0.54    ( ! [X10,X9] : (sK0 = X9 | sK0 = X10) )),
% 0.21/0.54    inference(resolution,[],[f264,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.21/0.54    inference(equality_resolution,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.54    inference(rectify,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.54    inference(flattening,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.54    inference(nnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.54  fof(f264,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK0,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f248,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f248,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r2_hidden(sK0,X0)) )),
% 0.21/0.54    inference(superposition,[],[f45,f184])).
% 0.21/0.54  fof(f184,plain,(
% 0.21/0.54    k1_xboole_0 = k2_tarski(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f97,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(resolution,[],[f38,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    v1_xboole_0(k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    v1_xboole_0(k2_tarski(sK0,sK1))),
% 0.21/0.54    inference(subsumption_resolution,[],[f96,f29])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_tarski(sK0,sK1))),
% 0.21/0.54    inference(superposition,[],[f37,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k2_tarski(sK0,sK1))),
% 0.21/0.54    inference(backward_demodulation,[],[f59,f79])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    k1_xboole_0 = sK2),
% 0.21/0.54    inference(resolution,[],[f68,f29])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X1] : (~v1_xboole_0(X1) | sK2 = X1) )),
% 0.21/0.54    inference(resolution,[],[f38,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    v1_xboole_0(sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f56,f29])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK2)),
% 0.21/0.54    inference(superposition,[],[f37,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.54    inference(negated_conjecture,[],[f13])).
% 0.21/0.54  fof(f13,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 0.21/0.54  % (3130)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    k1_xboole_0 = k2_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 0.21/0.54    inference(superposition,[],[f34,f28])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X1,X0)) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X1,X0)) | v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (~v1_xboole_0(X0) => ~v1_xboole_0(k2_xboole_0(X1,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.54    inference(nnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 0.21/0.54    inference(equality_resolution,[],[f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 0.21/0.54    inference(equality_resolution,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  % (3130)Refutation not found, incomplete strategy% (3130)------------------------------
% 0.21/0.54  % (3130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3130)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3130)Memory used [KB]: 6140
% 0.21/0.54  % (3130)Time elapsed: 0.138 s
% 0.21/0.54  % (3130)------------------------------
% 0.21/0.54  % (3130)------------------------------
% 0.21/0.54  fof(f373,plain,(
% 0.21/0.54    ( ! [X4,X1] : (~r2_hidden(X4,sK0) | X1 = X4) )),
% 0.21/0.54    inference(condensation,[],[f305])).
% 0.21/0.54  fof(f305,plain,(
% 0.21/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,sK0) | X0 = X4 | X1 = X4) )),
% 0.21/0.54    inference(backward_demodulation,[],[f52,f288])).
% 0.21/0.54  fof(f360,plain,(
% 0.21/0.54    ( ! [X1] : (k1_xboole_0 != k2_xboole_0(sK0,X1)) )),
% 0.21/0.54    inference(backward_demodulation,[],[f33,f288])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (3109)------------------------------
% 0.21/0.54  % (3109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3109)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (3109)Memory used [KB]: 1918
% 0.21/0.54  % (3109)Time elapsed: 0.084 s
% 0.21/0.54  % (3109)------------------------------
% 0.21/0.54  % (3109)------------------------------
% 0.21/0.54  % (3111)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (3114)Refutation not found, incomplete strategy% (3114)------------------------------
% 0.21/0.54  % (3114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3114)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3114)Memory used [KB]: 10618
% 0.21/0.54  % (3114)Time elapsed: 0.137 s
% 0.21/0.54  % (3114)------------------------------
% 0.21/0.54  % (3114)------------------------------
% 0.21/0.55  % (3101)Success in time 0.182 s
%------------------------------------------------------------------------------
