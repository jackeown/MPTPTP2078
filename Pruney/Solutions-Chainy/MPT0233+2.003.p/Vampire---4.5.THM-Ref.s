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
% DateTime   : Thu Dec  3 12:37:04 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   49 (  68 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   85 ( 119 expanded)
%              Number of equality atoms :   47 (  74 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f388,plain,(
    $false ),
    inference(subsumption_resolution,[],[f387,f94])).

fof(f94,plain,(
    ! [X1] : k2_tarski(X1,X1) != k5_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)) ),
    inference(forward_demodulation,[],[f93,f41])).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f93,plain,(
    ! [X1] : k2_tarski(X1,X1) != k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1))) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_tarski(X0,X0) != k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) ) ),
    inference(definition_unfolding,[],[f72,f61,f63,f61,f61])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f61,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f387,plain,(
    k2_tarski(sK0,sK0) = k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) ),
    inference(backward_demodulation,[],[f310,f384])).

fof(f384,plain,(
    k2_tarski(sK0,sK0) = k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f368,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f368,plain,(
    r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK2,sK3)) ),
    inference(superposition,[],[f117,f81])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X0) = k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f60,f61,f61])).

fof(f60,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f117,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,k2_tarski(sK0,sK1)),k2_tarski(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f96,f37,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f37,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f96,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f47,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f310,plain,(
    k2_tarski(sK0,sK0) = k5_xboole_0(k2_tarski(sK0,sK0),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK2,sK3))) ),
    inference(unit_resulting_resolution,[],[f206,f88])).

fof(f88,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,X2)
      | k2_tarski(X1,X1) = k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),X2)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | X0 != X1
      | k2_tarski(X0,X0) = k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f50,f61,f63])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | X0 != X1
      | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f206,plain,(
    ~ r2_hidden(sK0,k2_tarski(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f143,f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f143,plain,(
    ~ sP5(sK0,sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f38,f39,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | X1 = X3
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f31])).

fof(f38,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (30997)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.49  % (30981)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (30978)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (30977)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (30976)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (30974)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (30979)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (30990)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (30991)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (30985)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (30984)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (30994)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (30996)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (30999)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (30988)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.37/0.53  % (30992)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.37/0.53  % (30993)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.37/0.53  % (30986)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.37/0.53  % (30983)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.37/0.54  % (30975)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.37/0.54  % (30980)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.54  % (30975)Refutation not found, incomplete strategy% (30975)------------------------------
% 1.37/0.54  % (30975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (30975)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (30975)Memory used [KB]: 1663
% 1.37/0.54  % (30975)Time elapsed: 0.124 s
% 1.37/0.54  % (30975)------------------------------
% 1.37/0.54  % (30975)------------------------------
% 1.37/0.54  % (31003)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.37/0.54  % (31001)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.37/0.54  % (30989)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.37/0.54  % (31000)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.37/0.54  % (31002)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.37/0.55  % (30995)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.50/0.55  % (30998)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.50/0.55  % (30982)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.50/0.55  % (30987)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.50/0.56  % (30993)Refutation found. Thanks to Tanya!
% 1.50/0.56  % SZS status Theorem for theBenchmark
% 1.50/0.56  % SZS output start Proof for theBenchmark
% 1.50/0.56  fof(f388,plain,(
% 1.50/0.56    $false),
% 1.50/0.56    inference(subsumption_resolution,[],[f387,f94])).
% 1.50/0.56  fof(f94,plain,(
% 1.50/0.56    ( ! [X1] : (k2_tarski(X1,X1) != k5_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1))) )),
% 1.50/0.56    inference(forward_demodulation,[],[f93,f41])).
% 1.50/0.56  fof(f41,plain,(
% 1.50/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.50/0.56    inference(cnf_transformation,[],[f29])).
% 1.50/0.56  fof(f29,plain,(
% 1.50/0.56    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.50/0.56    inference(rectify,[],[f3])).
% 1.50/0.56  fof(f3,axiom,(
% 1.50/0.56    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.50/0.56  fof(f93,plain,(
% 1.50/0.56    ( ! [X1] : (k2_tarski(X1,X1) != k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)))) )),
% 1.50/0.56    inference(equality_resolution,[],[f84])).
% 1.50/0.56  fof(f84,plain,(
% 1.50/0.56    ( ! [X0,X1] : (X0 != X1 | k2_tarski(X0,X0) != k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)))) )),
% 1.50/0.56    inference(definition_unfolding,[],[f72,f61,f63,f61,f61])).
% 1.50/0.56  fof(f63,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f7])).
% 1.50/0.56  fof(f7,axiom,(
% 1.50/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.50/0.56  fof(f61,plain,(
% 1.50/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f17])).
% 1.50/0.56  fof(f17,axiom,(
% 1.50/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.50/0.56  fof(f72,plain,(
% 1.50/0.56    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f26])).
% 1.50/0.56  fof(f26,axiom,(
% 1.50/0.56    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.50/0.56  fof(f387,plain,(
% 1.50/0.56    k2_tarski(sK0,sK0) = k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))),
% 1.50/0.56    inference(backward_demodulation,[],[f310,f384])).
% 1.50/0.56  fof(f384,plain,(
% 1.50/0.56    k2_tarski(sK0,sK0) = k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK2,sK3))),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f368,f46])).
% 1.50/0.56  fof(f46,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.50/0.56    inference(cnf_transformation,[],[f34])).
% 1.50/0.56  fof(f34,plain,(
% 1.50/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.50/0.56    inference(ennf_transformation,[],[f10])).
% 1.50/0.56  fof(f10,axiom,(
% 1.50/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.50/0.56  fof(f368,plain,(
% 1.50/0.56    r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK2,sK3))),
% 1.50/0.56    inference(superposition,[],[f117,f81])).
% 1.50/0.56  fof(f81,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k2_tarski(X0,X0) = k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))) )),
% 1.50/0.56    inference(definition_unfolding,[],[f60,f61,f61])).
% 1.50/0.56  fof(f60,plain,(
% 1.50/0.56    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f25])).
% 1.50/0.56  fof(f25,axiom,(
% 1.50/0.56    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 1.50/0.57  fof(f117,plain,(
% 1.50/0.57    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k2_tarski(sK0,sK1)),k2_tarski(sK2,sK3))) )),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f96,f37,f42])).
% 1.50/0.57  fof(f42,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f33])).
% 1.50/0.57  fof(f33,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.50/0.57    inference(flattening,[],[f32])).
% 1.50/0.57  fof(f32,plain,(
% 1.50/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.50/0.57    inference(ennf_transformation,[],[f9])).
% 1.50/0.57  fof(f9,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.50/0.57  fof(f37,plain,(
% 1.50/0.57    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.50/0.57    inference(cnf_transformation,[],[f31])).
% 1.50/0.57  fof(f31,plain,(
% 1.50/0.57    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.50/0.57    inference(ennf_transformation,[],[f28])).
% 1.50/0.57  fof(f28,negated_conjecture,(
% 1.50/0.57    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.50/0.57    inference(negated_conjecture,[],[f27])).
% 1.50/0.57  fof(f27,conjecture,(
% 1.50/0.57    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 1.50/0.57  fof(f96,plain,(
% 1.50/0.57    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 1.50/0.57    inference(superposition,[],[f47,f40])).
% 1.50/0.57  fof(f40,plain,(
% 1.50/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f2])).
% 1.50/0.57  fof(f2,axiom,(
% 1.50/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.50/0.57  fof(f47,plain,(
% 1.50/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f8])).
% 1.50/0.57  fof(f8,axiom,(
% 1.50/0.57    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.50/0.57  fof(f310,plain,(
% 1.50/0.57    k2_tarski(sK0,sK0) = k5_xboole_0(k2_tarski(sK0,sK0),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK2,sK3)))),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f206,f88])).
% 1.50/0.57  fof(f88,plain,(
% 1.50/0.57    ( ! [X2,X1] : (r2_hidden(X1,X2) | k2_tarski(X1,X1) = k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),X2))) )),
% 1.50/0.57    inference(equality_resolution,[],[f79])).
% 1.50/0.57  fof(f79,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | X0 != X1 | k2_tarski(X0,X0) = k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),X2))) )),
% 1.50/0.57    inference(definition_unfolding,[],[f50,f61,f63])).
% 1.50/0.57  fof(f50,plain,(
% 1.50/0.57    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | X0 != X1 | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f24])).
% 1.50/0.57  fof(f24,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 1.50/0.57  fof(f206,plain,(
% 1.50/0.57    ~r2_hidden(sK0,k2_tarski(sK2,sK3))),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f143,f89])).
% 1.50/0.57  fof(f89,plain,(
% 1.50/0.57    ( ! [X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,k2_tarski(X0,X1))) )),
% 1.50/0.57    inference(equality_resolution,[],[f57])).
% 1.50/0.57  fof(f57,plain,(
% 1.50/0.57    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.50/0.57    inference(cnf_transformation,[],[f15])).
% 1.50/0.57  fof(f15,axiom,(
% 1.50/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.50/0.57  fof(f143,plain,(
% 1.50/0.57    ~sP5(sK0,sK3,sK2)),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f38,f39,f55])).
% 1.50/0.57  fof(f55,plain,(
% 1.50/0.57    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | X1 = X3 | X0 = X3) )),
% 1.50/0.57    inference(cnf_transformation,[],[f15])).
% 1.50/0.57  fof(f39,plain,(
% 1.50/0.57    sK0 != sK3),
% 1.50/0.57    inference(cnf_transformation,[],[f31])).
% 1.50/0.57  fof(f38,plain,(
% 1.50/0.57    sK0 != sK2),
% 1.50/0.57    inference(cnf_transformation,[],[f31])).
% 1.50/0.57  % SZS output end Proof for theBenchmark
% 1.50/0.57  % (30993)------------------------------
% 1.50/0.57  % (30993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (30993)Termination reason: Refutation
% 1.50/0.57  
% 1.50/0.57  % (30993)Memory used [KB]: 2046
% 1.50/0.57  % (30993)Time elapsed: 0.130 s
% 1.50/0.57  % (30993)------------------------------
% 1.50/0.57  % (30993)------------------------------
% 1.50/0.57  % (30973)Success in time 0.207 s
%------------------------------------------------------------------------------
