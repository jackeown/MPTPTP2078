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
% DateTime   : Thu Dec  3 12:35:31 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   54 (  67 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :   12
%              Number of atoms          :   72 (  92 expanded)
%              Number of equality atoms :   55 (  73 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1878,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f31,f1773,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f1773,plain,(
    r1_tarski(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f56,f1656])).

fof(f1656,plain,(
    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f1606,f30])).

fof(f30,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f1606,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(backward_demodulation,[],[f111,f1605])).

fof(f1605,plain,(
    ! [X19,X18] : k2_xboole_0(k3_xboole_0(X18,X19),X18) = X18 ),
    inference(forward_demodulation,[],[f1573,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f1573,plain,(
    ! [X19,X18] : k2_xboole_0(k3_xboole_0(X18,X19),X18) = k2_xboole_0(k3_xboole_0(X18,X19),k4_xboole_0(X18,X19)) ),
    inference(superposition,[],[f198,f292])).

fof(f292,plain,(
    ! [X8,X7] : k4_xboole_0(X7,X8) = k4_xboole_0(X7,k3_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f285,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f285,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k3_xboole_0(X7,X8)) = k5_xboole_0(X7,k3_xboole_0(X7,X8)) ),
    inference(superposition,[],[f71,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f45,f36])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f71,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f41,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f198,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f197,f32])).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f197,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X4,X3)) = k5_xboole_0(k2_xboole_0(X3,X4),k1_xboole_0) ),
    inference(backward_demodulation,[],[f97,f182])).

fof(f182,plain,(
    ! [X2,X3] : k1_xboole_0 = k3_xboole_0(X3,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f65,f38])).

fof(f65,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(resolution,[],[f49,f35])).

fof(f35,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f97,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X4,X3)) = k5_xboole_0(k2_xboole_0(X3,X4),k3_xboole_0(X3,k4_xboole_0(X4,X3))) ),
    inference(superposition,[],[f44,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f111,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f52,f34])).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f52,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f56,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f36,f38])).

fof(f31,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (32337)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (32329)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (32326)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (32334)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (32352)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (32351)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (32324)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (32335)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (32331)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (32344)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (32347)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (32336)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (32327)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (32336)Refutation not found, incomplete strategy% (32336)------------------------------
% 0.21/0.55  % (32336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32336)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32336)Memory used [KB]: 10618
% 0.21/0.55  % (32336)Time elapsed: 0.147 s
% 0.21/0.55  % (32336)------------------------------
% 0.21/0.55  % (32336)------------------------------
% 0.21/0.55  % (32348)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (32343)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (32328)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.56  % (32340)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (32340)Refutation not found, incomplete strategy% (32340)------------------------------
% 0.21/0.56  % (32340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32330)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (32340)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (32340)Memory used [KB]: 10618
% 0.21/0.56  % (32340)Time elapsed: 0.141 s
% 0.21/0.56  % (32340)------------------------------
% 0.21/0.56  % (32340)------------------------------
% 0.21/0.56  % (32325)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.56  % (32345)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  % (32325)Refutation not found, incomplete strategy% (32325)------------------------------
% 0.21/0.56  % (32325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32325)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (32325)Memory used [KB]: 1663
% 0.21/0.56  % (32325)Time elapsed: 0.154 s
% 0.21/0.56  % (32325)------------------------------
% 0.21/0.56  % (32325)------------------------------
% 0.21/0.57  % (32349)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.57  % (32350)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (32338)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.57  % (32339)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.58  % (32342)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.58  % (32333)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.58  % (32332)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.58  % (32353)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.58  % (32353)Refutation not found, incomplete strategy% (32353)------------------------------
% 0.21/0.58  % (32353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (32353)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (32353)Memory used [KB]: 1663
% 0.21/0.58  % (32353)Time elapsed: 0.002 s
% 0.21/0.58  % (32353)------------------------------
% 0.21/0.58  % (32353)------------------------------
% 0.21/0.59  % (32341)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.59  % (32346)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 2.04/0.64  % (32331)Refutation found. Thanks to Tanya!
% 2.04/0.64  % SZS status Theorem for theBenchmark
% 2.04/0.64  % SZS output start Proof for theBenchmark
% 2.04/0.64  fof(f1878,plain,(
% 2.04/0.64    $false),
% 2.04/0.64    inference(unit_resulting_resolution,[],[f31,f1773,f46])).
% 2.04/0.64  fof(f46,plain,(
% 2.04/0.64    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 2.04/0.64    inference(cnf_transformation,[],[f25])).
% 2.04/0.64  fof(f25,plain,(
% 2.04/0.64    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 2.04/0.64    inference(ennf_transformation,[],[f19])).
% 2.04/0.64  fof(f19,axiom,(
% 2.04/0.64    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 2.04/0.64  fof(f1773,plain,(
% 2.04/0.64    r1_tarski(k1_tarski(sK1),k1_tarski(sK0))),
% 2.04/0.64    inference(superposition,[],[f56,f1656])).
% 2.04/0.64  fof(f1656,plain,(
% 2.04/0.64    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 2.04/0.64    inference(superposition,[],[f1606,f30])).
% 2.04/0.64  fof(f30,plain,(
% 2.04/0.64    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 2.04/0.64    inference(cnf_transformation,[],[f27])).
% 2.04/0.64  fof(f27,plain,(
% 2.04/0.64    sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 2.04/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26])).
% 2.04/0.64  fof(f26,plain,(
% 2.04/0.64    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 2.04/0.64    introduced(choice_axiom,[])).
% 2.04/0.64  fof(f23,plain,(
% 2.04/0.64    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 2.04/0.64    inference(ennf_transformation,[],[f21])).
% 2.04/0.64  fof(f21,negated_conjecture,(
% 2.04/0.64    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.04/0.64    inference(negated_conjecture,[],[f20])).
% 2.04/0.64  fof(f20,conjecture,(
% 2.04/0.64    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 2.04/0.64  fof(f1606,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0) )),
% 2.04/0.64    inference(backward_demodulation,[],[f111,f1605])).
% 2.04/0.64  fof(f1605,plain,(
% 2.04/0.64    ( ! [X19,X18] : (k2_xboole_0(k3_xboole_0(X18,X19),X18) = X18) )),
% 2.04/0.64    inference(forward_demodulation,[],[f1573,f43])).
% 2.04/0.64  fof(f43,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.04/0.64    inference(cnf_transformation,[],[f10])).
% 2.04/0.64  fof(f10,axiom,(
% 2.04/0.64    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.04/0.64  fof(f1573,plain,(
% 2.04/0.64    ( ! [X19,X18] : (k2_xboole_0(k3_xboole_0(X18,X19),X18) = k2_xboole_0(k3_xboole_0(X18,X19),k4_xboole_0(X18,X19))) )),
% 2.04/0.64    inference(superposition,[],[f198,f292])).
% 2.04/0.64  fof(f292,plain,(
% 2.04/0.64    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k4_xboole_0(X7,k3_xboole_0(X7,X8))) )),
% 2.04/0.64    inference(forward_demodulation,[],[f285,f41])).
% 2.04/0.64  fof(f41,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.04/0.64    inference(cnf_transformation,[],[f4])).
% 2.04/0.64  fof(f4,axiom,(
% 2.04/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.04/0.64  fof(f285,plain,(
% 2.04/0.64    ( ! [X8,X7] : (k4_xboole_0(X7,k3_xboole_0(X7,X8)) = k5_xboole_0(X7,k3_xboole_0(X7,X8))) )),
% 2.04/0.64    inference(superposition,[],[f71,f61])).
% 2.04/0.64  fof(f61,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 2.04/0.64    inference(resolution,[],[f45,f36])).
% 2.04/0.64  fof(f36,plain,(
% 2.04/0.64    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f5])).
% 2.04/0.64  fof(f5,axiom,(
% 2.04/0.64    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.04/0.64  fof(f45,plain,(
% 2.04/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.04/0.64    inference(cnf_transformation,[],[f24])).
% 2.04/0.64  fof(f24,plain,(
% 2.04/0.64    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.04/0.64    inference(ennf_transformation,[],[f8])).
% 2.04/0.64  fof(f8,axiom,(
% 2.04/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.04/0.64  fof(f71,plain,(
% 2.04/0.64    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 2.04/0.64    inference(superposition,[],[f41,f38])).
% 2.04/0.64  fof(f38,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f1])).
% 2.04/0.64  fof(f1,axiom,(
% 2.04/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.04/0.64  fof(f198,plain,(
% 2.04/0.64    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 2.04/0.64    inference(forward_demodulation,[],[f197,f32])).
% 2.04/0.64  fof(f32,plain,(
% 2.04/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.04/0.64    inference(cnf_transformation,[],[f11])).
% 2.04/0.64  fof(f11,axiom,(
% 2.04/0.64    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.04/0.64  fof(f197,plain,(
% 2.04/0.64    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X4,X3)) = k5_xboole_0(k2_xboole_0(X3,X4),k1_xboole_0)) )),
% 2.04/0.64    inference(backward_demodulation,[],[f97,f182])).
% 2.04/0.64  fof(f182,plain,(
% 2.04/0.64    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(X3,k4_xboole_0(X2,X3))) )),
% 2.04/0.64    inference(superposition,[],[f65,f38])).
% 2.04/0.64  fof(f65,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.04/0.64    inference(resolution,[],[f49,f35])).
% 2.04/0.64  fof(f35,plain,(
% 2.04/0.64    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.04/0.64    inference(cnf_transformation,[],[f12])).
% 2.04/0.64  fof(f12,axiom,(
% 2.04/0.64    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.04/0.64  fof(f49,plain,(
% 2.04/0.64    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.04/0.64    inference(cnf_transformation,[],[f29])).
% 2.04/0.64  fof(f29,plain,(
% 2.04/0.64    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.04/0.64    inference(nnf_transformation,[],[f2])).
% 2.04/0.64  fof(f2,axiom,(
% 2.04/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.04/0.64  fof(f97,plain,(
% 2.04/0.64    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X4,X3)) = k5_xboole_0(k2_xboole_0(X3,X4),k3_xboole_0(X3,k4_xboole_0(X4,X3)))) )),
% 2.04/0.64    inference(superposition,[],[f44,f42])).
% 2.04/0.64  fof(f42,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.04/0.64    inference(cnf_transformation,[],[f15])).
% 2.04/0.64  fof(f15,axiom,(
% 2.04/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.04/0.64  fof(f44,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.04/0.64    inference(cnf_transformation,[],[f14])).
% 2.04/0.64  fof(f14,axiom,(
% 2.04/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 2.04/0.64  fof(f111,plain,(
% 2.04/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 2.04/0.64    inference(superposition,[],[f52,f34])).
% 2.04/0.64  fof(f34,plain,(
% 2.04/0.64    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.04/0.64    inference(cnf_transformation,[],[f22])).
% 2.04/0.64  fof(f22,plain,(
% 2.04/0.64    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.04/0.64    inference(rectify,[],[f3])).
% 2.04/0.64  fof(f3,axiom,(
% 2.04/0.64    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.04/0.64  fof(f52,plain,(
% 2.04/0.64    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 2.04/0.64    inference(cnf_transformation,[],[f7])).
% 2.04/0.64  fof(f7,axiom,(
% 2.04/0.64    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.04/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 2.04/0.64  fof(f56,plain,(
% 2.04/0.64    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 2.04/0.64    inference(superposition,[],[f36,f38])).
% 2.04/0.64  fof(f31,plain,(
% 2.04/0.64    sK0 != sK1),
% 2.04/0.64    inference(cnf_transformation,[],[f27])).
% 2.04/0.64  % SZS output end Proof for theBenchmark
% 2.04/0.64  % (32331)------------------------------
% 2.04/0.64  % (32331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.64  % (32331)Termination reason: Refutation
% 2.04/0.64  
% 2.04/0.64  % (32331)Memory used [KB]: 2942
% 2.04/0.64  % (32331)Time elapsed: 0.206 s
% 2.04/0.64  % (32331)------------------------------
% 2.04/0.64  % (32331)------------------------------
% 2.04/0.64  % (32323)Success in time 0.283 s
%------------------------------------------------------------------------------
