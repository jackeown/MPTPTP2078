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
% DateTime   : Thu Dec  3 12:32:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   45 (  66 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :   12
%              Number of atoms          :   66 ( 119 expanded)
%              Number of equality atoms :   23 (  31 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1174,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1167,f696])).

fof(f696,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f36,f683])).

fof(f683,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f610,f35])).

fof(f35,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f610,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X6,k4_xboole_0(X5,X4))
      | r1_xboole_0(X6,X4) ) ),
    inference(superposition,[],[f55,f590])).

fof(f590,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X8,X7)) = X7 ),
    inference(forward_demodulation,[],[f576,f39])).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f576,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X8,X7)) = k5_xboole_0(X7,k1_xboole_0) ),
    inference(superposition,[],[f47,f525])).

fof(f525,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f52,f174])).

fof(f174,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f168,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f168,plain,(
    ! [X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X0) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f47,f73])).

fof(f73,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k3_xboole_0(k3_xboole_0(X5,X6),X5) ),
    inference(resolution,[],[f48,f43])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f36,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f1167,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f1001,f76])).

fof(f76,plain,(
    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f48,f35])).

fof(f1001,plain,(
    ! [X39,X37,X38] : r1_tarski(k3_xboole_0(X39,k4_xboole_0(X37,X38)),X37) ),
    inference(superposition,[],[f931,f75])).

fof(f75,plain,(
    ! [X10,X9] : k4_xboole_0(X9,X10) = k3_xboole_0(k4_xboole_0(X9,X10),X9) ),
    inference(resolution,[],[f48,f42])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f931,plain,(
    ! [X24,X23,X22] : r1_tarski(k3_xboole_0(X22,k3_xboole_0(X23,X24)),X24) ),
    inference(superposition,[],[f63,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f63,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f43,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:20:33 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (3344)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (3352)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (3346)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (3349)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (3343)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (3363)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (3348)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (3366)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (3358)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (3353)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (3358)Refutation not found, incomplete strategy% (3358)------------------------------
% 0.21/0.53  % (3358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3358)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3358)Memory used [KB]: 6140
% 0.21/0.53  % (3358)Time elapsed: 0.004 s
% 0.21/0.53  % (3358)------------------------------
% 0.21/0.53  % (3358)------------------------------
% 0.21/0.53  % (3350)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (3355)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (3371)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (3345)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (3367)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (3354)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (3347)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (3360)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (3369)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (3357)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (3365)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (3359)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (3365)Refutation not found, incomplete strategy% (3365)------------------------------
% 0.21/0.55  % (3365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3365)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3365)Memory used [KB]: 10746
% 0.21/0.55  % (3365)Time elapsed: 0.149 s
% 0.21/0.55  % (3365)------------------------------
% 0.21/0.55  % (3365)------------------------------
% 0.21/0.55  % (3368)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (3370)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (3372)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (3351)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (3362)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (3360)Refutation not found, incomplete strategy% (3360)------------------------------
% 0.21/0.56  % (3360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3360)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (3360)Memory used [KB]: 10618
% 0.21/0.56  % (3360)Time elapsed: 0.152 s
% 0.21/0.56  % (3360)------------------------------
% 0.21/0.56  % (3360)------------------------------
% 0.21/0.56  % (3364)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (3361)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.57  % (3356)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.59  % (3350)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 1.79/0.61  % SZS output start Proof for theBenchmark
% 1.79/0.61  fof(f1174,plain,(
% 1.79/0.61    $false),
% 1.79/0.61    inference(subsumption_resolution,[],[f1167,f696])).
% 1.79/0.61  fof(f696,plain,(
% 1.79/0.61    ~r1_tarski(sK0,sK1)),
% 1.79/0.61    inference(subsumption_resolution,[],[f36,f683])).
% 1.79/0.61  fof(f683,plain,(
% 1.79/0.61    r1_xboole_0(sK0,sK2)),
% 1.79/0.61    inference(resolution,[],[f610,f35])).
% 1.79/0.61  fof(f35,plain,(
% 1.79/0.61    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.79/0.61    inference(cnf_transformation,[],[f30])).
% 1.79/0.61  fof(f30,plain,(
% 1.79/0.61    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.79/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f29])).
% 1.79/0.61  fof(f29,plain,(
% 1.79/0.61    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 1.79/0.61    introduced(choice_axiom,[])).
% 1.79/0.61  fof(f23,plain,(
% 1.79/0.61    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.79/0.61    inference(ennf_transformation,[],[f21])).
% 1.79/0.61  fof(f21,negated_conjecture,(
% 1.79/0.61    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.79/0.61    inference(negated_conjecture,[],[f20])).
% 1.79/0.61  fof(f20,conjecture,(
% 1.79/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.79/0.61  fof(f610,plain,(
% 1.79/0.61    ( ! [X6,X4,X5] : (~r1_tarski(X6,k4_xboole_0(X5,X4)) | r1_xboole_0(X6,X4)) )),
% 1.79/0.61    inference(superposition,[],[f55,f590])).
% 1.79/0.61  fof(f590,plain,(
% 1.79/0.61    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X8,X7)) = X7) )),
% 1.79/0.61    inference(forward_demodulation,[],[f576,f39])).
% 1.79/0.61  fof(f39,plain,(
% 1.79/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.79/0.61    inference(cnf_transformation,[],[f16])).
% 1.79/0.61  fof(f16,axiom,(
% 1.79/0.61    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.79/0.61  fof(f576,plain,(
% 1.79/0.61    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X8,X7)) = k5_xboole_0(X7,k1_xboole_0)) )),
% 1.79/0.61    inference(superposition,[],[f47,f525])).
% 1.79/0.61  fof(f525,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.79/0.61    inference(superposition,[],[f52,f174])).
% 1.79/0.61  fof(f174,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 1.79/0.61    inference(forward_demodulation,[],[f168,f38])).
% 1.79/0.61  fof(f38,plain,(
% 1.79/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f18])).
% 1.79/0.61  fof(f18,axiom,(
% 1.79/0.61    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.79/0.61  fof(f168,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X0) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.79/0.61    inference(superposition,[],[f47,f73])).
% 1.79/0.61  fof(f73,plain,(
% 1.79/0.61    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k3_xboole_0(k3_xboole_0(X5,X6),X5)) )),
% 1.79/0.61    inference(resolution,[],[f48,f43])).
% 1.79/0.61  fof(f43,plain,(
% 1.79/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f9])).
% 1.79/0.61  fof(f9,axiom,(
% 1.79/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.79/0.61  fof(f48,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.79/0.61    inference(cnf_transformation,[],[f25])).
% 1.79/0.61  fof(f25,plain,(
% 1.79/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.79/0.61    inference(ennf_transformation,[],[f12])).
% 1.79/0.61  fof(f12,axiom,(
% 1.79/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.79/0.61  fof(f52,plain,(
% 1.79/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f14])).
% 1.79/0.61  fof(f14,axiom,(
% 1.79/0.61    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.79/0.61  fof(f47,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.79/0.61    inference(cnf_transformation,[],[f7])).
% 1.79/0.61  fof(f7,axiom,(
% 1.79/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.79/0.61  fof(f55,plain,(
% 1.79/0.61    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f26])).
% 1.79/0.61  fof(f26,plain,(
% 1.79/0.61    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.79/0.61    inference(ennf_transformation,[],[f17])).
% 1.79/0.61  fof(f17,axiom,(
% 1.79/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.79/0.61  fof(f36,plain,(
% 1.79/0.61    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 1.79/0.61    inference(cnf_transformation,[],[f30])).
% 1.79/0.61  fof(f1167,plain,(
% 1.79/0.61    r1_tarski(sK0,sK1)),
% 1.79/0.61    inference(superposition,[],[f1001,f76])).
% 1.79/0.61  fof(f76,plain,(
% 1.79/0.61    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.79/0.61    inference(resolution,[],[f48,f35])).
% 1.79/0.61  fof(f1001,plain,(
% 1.79/0.61    ( ! [X39,X37,X38] : (r1_tarski(k3_xboole_0(X39,k4_xboole_0(X37,X38)),X37)) )),
% 1.79/0.61    inference(superposition,[],[f931,f75])).
% 1.79/0.61  fof(f75,plain,(
% 1.79/0.61    ( ! [X10,X9] : (k4_xboole_0(X9,X10) = k3_xboole_0(k4_xboole_0(X9,X10),X9)) )),
% 1.79/0.61    inference(resolution,[],[f48,f42])).
% 1.79/0.61  fof(f42,plain,(
% 1.79/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f13])).
% 1.79/0.61  fof(f13,axiom,(
% 1.79/0.61    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.79/0.61  fof(f931,plain,(
% 1.79/0.61    ( ! [X24,X23,X22] : (r1_tarski(k3_xboole_0(X22,k3_xboole_0(X23,X24)),X24)) )),
% 1.79/0.61    inference(superposition,[],[f63,f53])).
% 1.79/0.61  fof(f53,plain,(
% 1.79/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.79/0.61    inference(cnf_transformation,[],[f8])).
% 1.79/0.61  fof(f8,axiom,(
% 1.79/0.61    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.79/0.61  fof(f63,plain,(
% 1.79/0.61    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 1.79/0.61    inference(superposition,[],[f43,f44])).
% 1.79/0.61  fof(f44,plain,(
% 1.79/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f1])).
% 1.79/0.61  fof(f1,axiom,(
% 1.79/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.79/0.61  % SZS output end Proof for theBenchmark
% 1.79/0.61  % (3350)------------------------------
% 1.79/0.61  % (3350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.61  % (3350)Termination reason: Refutation
% 1.79/0.61  
% 1.79/0.61  % (3350)Memory used [KB]: 7036
% 1.79/0.61  % (3350)Time elapsed: 0.150 s
% 1.79/0.61  % (3350)------------------------------
% 1.79/0.61  % (3350)------------------------------
% 1.79/0.61  % (3342)Success in time 0.247 s
%------------------------------------------------------------------------------
