%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:37 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 175 expanded)
%              Number of leaves         :   12 (  47 expanded)
%              Depth                    :   18
%              Number of atoms          :   95 ( 379 expanded)
%              Number of equality atoms :   42 ( 173 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1142,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1123,f874])).

fof(f874,plain,(
    ~ r1_xboole_0(k1_tarski(sK1),sK0) ),
    inference(resolution,[],[f867,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f867,plain,(
    r2_hidden(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f866])).

fof(f866,plain,
    ( sK0 != sK0
    | r2_hidden(sK1,sK0) ),
    inference(backward_demodulation,[],[f34,f865])).

fof(f865,plain,(
    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f850,f35])).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f850,plain,(
    k4_xboole_0(sK0,k1_tarski(sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f42,f492])).

fof(f492,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f491,f284])).

fof(f284,plain,
    ( r1_xboole_0(k1_tarski(sK1),sK0)
    | k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(superposition,[],[f58,f261])).

fof(f261,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(superposition,[],[f106,f75])).

fof(f75,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k2_xboole_0(k1_tarski(sK1),sK0),sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(resolution,[],[f46,f61])).

fof(f61,plain,
    ( r1_xboole_0(k1_tarski(sK1),sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(resolution,[],[f43,f33])).

fof(f33,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( r2_hidden(sK1,sK0)
      | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
    & ( ~ r2_hidden(sK1,sK0)
      | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK1,sK0)
        | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
      & ( ~ r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f106,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f68,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f68,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X1,X2),X1) ),
    inference(resolution,[],[f51,f37])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f45,f38])).

fof(f38,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f491,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1))
    | ~ r1_xboole_0(k1_tarski(sK1),sK0) ),
    inference(resolution,[],[f290,f52])).

fof(f290,plain,
    ( r2_hidden(sK1,sK0)
    | k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(trivial_inequality_removal,[],[f281])).

fof(f281,plain,
    ( sK0 != sK0
    | r2_hidden(sK1,sK0)
    | k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(superposition,[],[f34,f261])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f34,plain,
    ( sK0 != k4_xboole_0(sK0,k1_tarski(sK1))
    | r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f1123,plain,(
    r1_xboole_0(k1_tarski(sK1),sK0) ),
    inference(superposition,[],[f58,f865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:11:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (22511)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (22503)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (22503)Refutation not found, incomplete strategy% (22503)------------------------------
% 0.21/0.52  % (22503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22503)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22503)Memory used [KB]: 1663
% 0.21/0.52  % (22503)Time elapsed: 0.057 s
% 0.21/0.52  % (22503)------------------------------
% 0.21/0.52  % (22503)------------------------------
% 0.21/0.53  % (22495)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (22489)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.32/0.54  % (22491)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.32/0.54  % (22493)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.32/0.54  % (22516)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.32/0.54  % (22490)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.32/0.54  % (22504)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.32/0.54  % (22492)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.32/0.54  % (22498)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.32/0.55  % (22494)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.32/0.55  % (22499)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.32/0.55  % (22499)Refutation not found, incomplete strategy% (22499)------------------------------
% 1.32/0.55  % (22499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (22499)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (22499)Memory used [KB]: 10618
% 1.32/0.55  % (22499)Time elapsed: 0.133 s
% 1.32/0.55  % (22499)------------------------------
% 1.32/0.55  % (22499)------------------------------
% 1.32/0.55  % (22496)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.32/0.55  % (22508)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.32/0.55  % (22514)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.32/0.55  % (22514)Refutation not found, incomplete strategy% (22514)------------------------------
% 1.32/0.55  % (22514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (22514)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (22514)Memory used [KB]: 6140
% 1.32/0.55  % (22514)Time elapsed: 0.137 s
% 1.32/0.55  % (22514)------------------------------
% 1.32/0.55  % (22514)------------------------------
% 1.32/0.56  % (22507)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.32/0.56  % (22500)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.32/0.56  % (22500)Refutation not found, incomplete strategy% (22500)------------------------------
% 1.32/0.56  % (22500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (22500)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (22500)Memory used [KB]: 6140
% 1.32/0.56  % (22500)Time elapsed: 0.146 s
% 1.32/0.56  % (22500)------------------------------
% 1.32/0.56  % (22500)------------------------------
% 1.32/0.56  % (22512)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.32/0.56  % (22515)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.32/0.56  % (22516)Refutation not found, incomplete strategy% (22516)------------------------------
% 1.32/0.56  % (22516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (22515)Refutation not found, incomplete strategy% (22515)------------------------------
% 1.32/0.56  % (22515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (22515)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (22515)Memory used [KB]: 6140
% 1.32/0.56  % (22515)Time elapsed: 0.146 s
% 1.32/0.56  % (22515)------------------------------
% 1.32/0.56  % (22515)------------------------------
% 1.32/0.56  % (22516)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (22516)Memory used [KB]: 6140
% 1.32/0.56  % (22516)Time elapsed: 0.147 s
% 1.32/0.56  % (22516)------------------------------
% 1.32/0.56  % (22516)------------------------------
% 1.32/0.56  % (22490)Refutation not found, incomplete strategy% (22490)------------------------------
% 1.32/0.56  % (22490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (22490)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (22490)Memory used [KB]: 1663
% 1.32/0.56  % (22490)Time elapsed: 0.142 s
% 1.32/0.56  % (22490)------------------------------
% 1.32/0.56  % (22490)------------------------------
% 1.49/0.56  % (22506)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.49/0.56  % (22506)Refutation not found, incomplete strategy% (22506)------------------------------
% 1.49/0.56  % (22506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (22506)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (22506)Memory used [KB]: 1791
% 1.49/0.56  % (22506)Time elapsed: 0.148 s
% 1.49/0.56  % (22506)------------------------------
% 1.49/0.56  % (22506)------------------------------
% 1.49/0.57  % (22507)Refutation not found, incomplete strategy% (22507)------------------------------
% 1.49/0.57  % (22507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (22507)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (22507)Memory used [KB]: 1663
% 1.49/0.57  % (22507)Time elapsed: 0.155 s
% 1.49/0.57  % (22507)------------------------------
% 1.49/0.57  % (22507)------------------------------
% 1.49/0.57  % (22501)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.49/0.57  % (22501)Refutation not found, incomplete strategy% (22501)------------------------------
% 1.49/0.57  % (22501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (22501)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (22501)Memory used [KB]: 10618
% 1.49/0.57  % (22501)Time elapsed: 0.156 s
% 1.49/0.57  % (22501)------------------------------
% 1.49/0.57  % (22501)------------------------------
% 1.49/0.57  % (22502)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.49/0.57  % (22517)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.49/0.58  % (22517)Refutation not found, incomplete strategy% (22517)------------------------------
% 1.49/0.58  % (22517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.58  % (22517)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.58  
% 1.49/0.58  % (22517)Memory used [KB]: 10618
% 1.49/0.58  % (22517)Time elapsed: 0.164 s
% 1.49/0.58  % (22517)------------------------------
% 1.49/0.58  % (22517)------------------------------
% 1.49/0.58  % (22509)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.49/0.58  % (22518)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.49/0.58  % (22518)Refutation not found, incomplete strategy% (22518)------------------------------
% 1.49/0.58  % (22518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.58  % (22518)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.58  
% 1.49/0.58  % (22518)Memory used [KB]: 1663
% 1.49/0.58  % (22518)Time elapsed: 0.001 s
% 1.49/0.58  % (22518)------------------------------
% 1.49/0.58  % (22518)------------------------------
% 1.49/0.58  % (22510)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.49/0.58  % (22497)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.49/0.60  % (22513)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.49/0.60  % (22505)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.49/0.60  % (22505)Refutation not found, incomplete strategy% (22505)------------------------------
% 1.49/0.60  % (22505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.60  % (22505)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.60  
% 1.49/0.60  % (22505)Memory used [KB]: 10618
% 1.49/0.60  % (22505)Time elapsed: 0.157 s
% 1.49/0.60  % (22505)------------------------------
% 1.49/0.60  % (22505)------------------------------
% 1.49/0.61  % (22513)Refutation not found, incomplete strategy% (22513)------------------------------
% 1.49/0.61  % (22513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.61  % (22513)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.61  
% 1.49/0.61  % (22513)Memory used [KB]: 10618
% 1.49/0.61  % (22513)Time elapsed: 0.156 s
% 1.49/0.61  % (22513)------------------------------
% 1.49/0.61  % (22513)------------------------------
% 1.49/0.61  % (22496)Refutation found. Thanks to Tanya!
% 1.49/0.61  % SZS status Theorem for theBenchmark
% 1.49/0.61  % SZS output start Proof for theBenchmark
% 1.49/0.61  fof(f1142,plain,(
% 1.49/0.61    $false),
% 1.49/0.61    inference(subsumption_resolution,[],[f1123,f874])).
% 1.49/0.61  fof(f874,plain,(
% 1.49/0.61    ~r1_xboole_0(k1_tarski(sK1),sK0)),
% 1.49/0.61    inference(resolution,[],[f867,f52])).
% 1.49/0.61  fof(f52,plain,(
% 1.49/0.61    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f26])).
% 1.49/0.61  fof(f26,plain,(
% 1.49/0.61    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.49/0.61    inference(ennf_transformation,[],[f16])).
% 1.49/0.61  fof(f16,axiom,(
% 1.49/0.61    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.49/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.49/0.61  fof(f867,plain,(
% 1.49/0.61    r2_hidden(sK1,sK0)),
% 1.49/0.61    inference(trivial_inequality_removal,[],[f866])).
% 1.49/0.61  fof(f866,plain,(
% 1.49/0.61    sK0 != sK0 | r2_hidden(sK1,sK0)),
% 1.49/0.61    inference(backward_demodulation,[],[f34,f865])).
% 1.49/0.61  fof(f865,plain,(
% 1.49/0.61    sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.49/0.61    inference(forward_demodulation,[],[f850,f35])).
% 1.49/0.61  fof(f35,plain,(
% 1.49/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.49/0.61    inference(cnf_transformation,[],[f9])).
% 1.49/0.61  fof(f9,axiom,(
% 1.49/0.61    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.49/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.49/0.61  fof(f850,plain,(
% 1.49/0.61    k4_xboole_0(sK0,k1_tarski(sK1)) = k5_xboole_0(sK0,k1_xboole_0)),
% 1.49/0.61    inference(superposition,[],[f42,f492])).
% 1.49/0.61  fof(f492,plain,(
% 1.49/0.61    k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1))),
% 1.49/0.61    inference(subsumption_resolution,[],[f491,f284])).
% 1.49/0.61  fof(f284,plain,(
% 1.49/0.61    r1_xboole_0(k1_tarski(sK1),sK0) | k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1))),
% 1.49/0.61    inference(superposition,[],[f58,f261])).
% 1.49/0.61  fof(f261,plain,(
% 1.49/0.61    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1))),
% 1.49/0.61    inference(superposition,[],[f106,f75])).
% 1.49/0.61  fof(f75,plain,(
% 1.49/0.61    k1_tarski(sK1) = k4_xboole_0(k2_xboole_0(k1_tarski(sK1),sK0),sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.49/0.61    inference(resolution,[],[f46,f61])).
% 1.49/0.61  fof(f61,plain,(
% 1.49/0.61    r1_xboole_0(k1_tarski(sK1),sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.49/0.61    inference(resolution,[],[f43,f33])).
% 1.49/0.61  fof(f33,plain,(
% 1.49/0.61    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.49/0.61    inference(cnf_transformation,[],[f29])).
% 1.49/0.61  fof(f29,plain,(
% 1.49/0.61    (r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 1.49/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).
% 1.49/0.61  fof(f28,plain,(
% 1.49/0.61    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))))),
% 1.49/0.61    introduced(choice_axiom,[])).
% 1.49/0.61  fof(f27,plain,(
% 1.49/0.61    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 1.49/0.61    inference(nnf_transformation,[],[f21])).
% 1.49/0.61  fof(f21,plain,(
% 1.49/0.61    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 1.49/0.61    inference(ennf_transformation,[],[f20])).
% 1.49/0.61  fof(f20,negated_conjecture,(
% 1.49/0.61    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.49/0.61    inference(negated_conjecture,[],[f19])).
% 1.49/0.61  fof(f19,conjecture,(
% 1.49/0.61    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.49/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.49/0.61  fof(f43,plain,(
% 1.49/0.61    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f22])).
% 1.49/0.61  fof(f22,plain,(
% 1.49/0.61    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.49/0.61    inference(ennf_transformation,[],[f17])).
% 1.49/0.61  fof(f17,axiom,(
% 1.49/0.61    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.49/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.49/0.61  fof(f46,plain,(
% 1.49/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0) )),
% 1.49/0.61    inference(cnf_transformation,[],[f25])).
% 1.49/0.61  fof(f25,plain,(
% 1.49/0.61    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.49/0.61    inference(ennf_transformation,[],[f11])).
% 1.49/0.61  fof(f11,axiom,(
% 1.49/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 1.49/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 1.49/0.61  fof(f106,plain,(
% 1.49/0.61    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.49/0.61    inference(superposition,[],[f68,f54])).
% 1.49/0.61  fof(f54,plain,(
% 1.49/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f8])).
% 1.49/0.61  fof(f8,axiom,(
% 1.49/0.61    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.49/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.49/0.61  fof(f68,plain,(
% 1.49/0.61    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X1,X2),X1)) )),
% 1.49/0.61    inference(resolution,[],[f51,f37])).
% 1.49/0.61  fof(f37,plain,(
% 1.49/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f6])).
% 1.49/0.61  fof(f6,axiom,(
% 1.49/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.49/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.49/0.61  fof(f51,plain,(
% 1.49/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.49/0.61    inference(cnf_transformation,[],[f32])).
% 1.49/0.61  fof(f32,plain,(
% 1.49/0.61    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.49/0.61    inference(nnf_transformation,[],[f4])).
% 1.49/0.61  fof(f4,axiom,(
% 1.49/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.49/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.49/0.61  fof(f58,plain,(
% 1.49/0.61    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.49/0.61    inference(resolution,[],[f45,f38])).
% 1.49/0.61  fof(f38,plain,(
% 1.49/0.61    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f10])).
% 1.49/0.61  fof(f10,axiom,(
% 1.49/0.61    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.49/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.49/0.61  fof(f45,plain,(
% 1.49/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f24])).
% 1.49/0.61  fof(f24,plain,(
% 1.49/0.61    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.49/0.61    inference(ennf_transformation,[],[f2])).
% 1.49/0.61  fof(f2,axiom,(
% 1.49/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.49/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.49/0.61  fof(f491,plain,(
% 1.49/0.61    k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1)) | ~r1_xboole_0(k1_tarski(sK1),sK0)),
% 1.49/0.61    inference(resolution,[],[f290,f52])).
% 1.49/0.61  fof(f290,plain,(
% 1.49/0.61    r2_hidden(sK1,sK0) | k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1))),
% 1.49/0.61    inference(trivial_inequality_removal,[],[f281])).
% 1.49/0.61  fof(f281,plain,(
% 1.49/0.61    sK0 != sK0 | r2_hidden(sK1,sK0) | k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1))),
% 1.49/0.61    inference(superposition,[],[f34,f261])).
% 1.49/0.61  fof(f42,plain,(
% 1.49/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.49/0.61    inference(cnf_transformation,[],[f5])).
% 1.49/0.61  fof(f5,axiom,(
% 1.49/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.49/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.49/0.61  fof(f34,plain,(
% 1.49/0.61    sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) | r2_hidden(sK1,sK0)),
% 1.49/0.61    inference(cnf_transformation,[],[f29])).
% 1.49/0.61  fof(f1123,plain,(
% 1.49/0.61    r1_xboole_0(k1_tarski(sK1),sK0)),
% 1.49/0.61    inference(superposition,[],[f58,f865])).
% 1.49/0.61  % SZS output end Proof for theBenchmark
% 1.49/0.61  % (22496)------------------------------
% 1.49/0.61  % (22496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.61  % (22496)Termination reason: Refutation
% 1.49/0.61  
% 1.49/0.61  % (22496)Memory used [KB]: 2430
% 1.49/0.61  % (22496)Time elapsed: 0.188 s
% 1.49/0.61  % (22496)------------------------------
% 1.49/0.61  % (22496)------------------------------
% 1.49/0.61  % (22488)Success in time 0.239 s
%------------------------------------------------------------------------------
