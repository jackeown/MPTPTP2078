%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:59 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   37 (  81 expanded)
%              Number of leaves         :    7 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :   75 ( 155 expanded)
%              Number of equality atoms :   10 (  40 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f898,plain,(
    $false ),
    inference(resolution,[],[f896,f21])).

fof(f21,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f896,plain,(
    ~ r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f805,f22])).

fof(f22,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f18])).

fof(f805,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    | ~ r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f153,f720])).

fof(f720,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))))
    | ~ r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f567,f123])).

fof(f123,plain,(
    ! [X14,X17,X15,X16] :
      ( r1_tarski(X17,k2_zfmisc_1(X14,k3_tarski(k2_tarski(X15,X16))))
      | ~ r1_tarski(X17,k2_zfmisc_1(X14,X16)) ) ),
    inference(superposition,[],[f36,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f27,f33,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f33])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f567,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5))))
    | ~ r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(resolution,[],[f134,f34])).

fof(f34,plain,(
    ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(definition_unfolding,[],[f23,f33,f33,f33])).

fof(f23,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f18])).

fof(f134,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( r1_tarski(k3_tarski(k2_tarski(X12,X13)),k2_zfmisc_1(k3_tarski(k2_tarski(X9,X11)),X10))
      | ~ r1_tarski(X13,k2_zfmisc_1(X11,X10))
      | ~ r1_tarski(X12,k2_zfmisc_1(X9,X10)) ) ),
    inference(superposition,[],[f35,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f26,f33,f33])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f33,f33])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

fof(f153,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k2_zfmisc_1(X0,k3_tarski(k2_tarski(X1,X2))))
      | ~ r1_tarski(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f89,f37])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_tarski(k2_tarski(X1,X0)))
      | ~ r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f36,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n016.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 11:00:49 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.18/0.49  % (9016)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.18/0.49  % (9004)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.18/0.50  % (9006)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.18/0.51  % (9014)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.18/0.51  % (9030)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.18/0.52  % (9031)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.18/0.52  % (9002)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.18/0.52  % (9007)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.53  % (9011)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.18/0.53  % (9023)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.18/0.53  % (9024)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.65/0.55  % (9017)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.65/0.56  % (9033)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.65/0.56  % (9025)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.65/0.56  % (9026)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.65/0.56  % (9018)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.78/0.57  % (9008)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.78/0.57  % (9001)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.78/0.57  % (9013)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.78/0.58  % (9027)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.78/0.58  % (9010)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.78/0.58  % (9005)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.78/0.58  % (9003)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.78/0.59  % (9022)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.78/0.59  % (9019)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.78/0.59  % (9015)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.78/0.60  % (9020)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.78/0.60  % (9029)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.78/0.60  % (9012)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.78/0.61  % (9004)Refutation not found, incomplete strategy% (9004)------------------------------
% 1.78/0.61  % (9004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.61  % (9006)Refutation found. Thanks to Tanya!
% 1.78/0.61  % SZS status Theorem for theBenchmark
% 1.78/0.61  % SZS output start Proof for theBenchmark
% 1.78/0.61  fof(f898,plain,(
% 1.78/0.61    $false),
% 1.78/0.61    inference(resolution,[],[f896,f21])).
% 1.78/0.61  fof(f21,plain,(
% 1.78/0.61    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.78/0.61    inference(cnf_transformation,[],[f18])).
% 1.78/0.61  fof(f18,plain,(
% 1.78/0.61    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.78/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f17])).
% 1.78/0.61  fof(f17,plain,(
% 1.78/0.61    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 1.78/0.61    introduced(choice_axiom,[])).
% 1.78/0.61  fof(f11,plain,(
% 1.78/0.61    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 1.78/0.61    inference(flattening,[],[f10])).
% 1.78/0.61  fof(f10,plain,(
% 1.78/0.61    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 1.78/0.61    inference(ennf_transformation,[],[f9])).
% 1.78/0.61  fof(f9,negated_conjecture,(
% 1.78/0.61    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 1.78/0.61    inference(negated_conjecture,[],[f8])).
% 1.78/0.61  fof(f8,conjecture,(
% 1.78/0.61    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 1.78/0.61  fof(f896,plain,(
% 1.78/0.61    ~r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.78/0.61    inference(resolution,[],[f805,f22])).
% 1.78/0.61  fof(f22,plain,(
% 1.78/0.61    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 1.78/0.61    inference(cnf_transformation,[],[f18])).
% 1.78/0.61  fof(f805,plain,(
% 1.78/0.61    ~r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) | ~r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.78/0.61    inference(resolution,[],[f153,f720])).
% 1.78/0.61  fof(f720,plain,(
% 1.78/0.61    ~r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5)))) | ~r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 1.78/0.61    inference(resolution,[],[f567,f123])).
% 1.78/0.61  fof(f123,plain,(
% 1.78/0.61    ( ! [X14,X17,X15,X16] : (r1_tarski(X17,k2_zfmisc_1(X14,k3_tarski(k2_tarski(X15,X16)))) | ~r1_tarski(X17,k2_zfmisc_1(X14,X16))) )),
% 1.78/0.61    inference(superposition,[],[f36,f37])).
% 1.78/0.61  fof(f37,plain,(
% 1.78/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 1.78/0.61    inference(definition_unfolding,[],[f27,f33,f33])).
% 1.78/0.61  fof(f33,plain,(
% 1.78/0.61    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f6])).
% 1.78/0.61  fof(f6,axiom,(
% 1.78/0.61    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.78/0.61  fof(f27,plain,(
% 1.78/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 1.78/0.61    inference(cnf_transformation,[],[f7])).
% 1.78/0.61  fof(f7,axiom,(
% 1.78/0.61    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 1.78/0.61  fof(f36,plain,(
% 1.78/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 1.78/0.61    inference(definition_unfolding,[],[f25,f33])).
% 1.78/0.61  fof(f25,plain,(
% 1.78/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f14])).
% 1.78/0.61  fof(f14,plain,(
% 1.78/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.78/0.61    inference(ennf_transformation,[],[f2])).
% 1.78/0.61  fof(f2,axiom,(
% 1.78/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.78/0.61  fof(f567,plain,(
% 1.78/0.61    ~r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) | ~r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))))),
% 1.78/0.61    inference(resolution,[],[f134,f34])).
% 1.78/0.61  fof(f34,plain,(
% 1.78/0.61    ~r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))),
% 1.78/0.61    inference(definition_unfolding,[],[f23,f33,f33,f33])).
% 1.78/0.61  fof(f23,plain,(
% 1.78/0.61    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 1.78/0.61    inference(cnf_transformation,[],[f18])).
% 1.78/0.61  fof(f134,plain,(
% 1.78/0.61    ( ! [X12,X10,X13,X11,X9] : (r1_tarski(k3_tarski(k2_tarski(X12,X13)),k2_zfmisc_1(k3_tarski(k2_tarski(X9,X11)),X10)) | ~r1_tarski(X13,k2_zfmisc_1(X11,X10)) | ~r1_tarski(X12,k2_zfmisc_1(X9,X10))) )),
% 1.78/0.61    inference(superposition,[],[f35,f38])).
% 1.78/0.61  fof(f38,plain,(
% 1.78/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 1.78/0.61    inference(definition_unfolding,[],[f26,f33,f33])).
% 1.78/0.61  fof(f26,plain,(
% 1.78/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 1.78/0.61    inference(cnf_transformation,[],[f7])).
% 1.78/0.61  fof(f35,plain,(
% 1.78/0.61    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.78/0.61    inference(definition_unfolding,[],[f24,f33,f33])).
% 1.78/0.61  fof(f24,plain,(
% 1.78/0.61    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f13])).
% 1.78/0.61  fof(f13,plain,(
% 1.78/0.61    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 1.78/0.61    inference(flattening,[],[f12])).
% 1.78/0.61  fof(f12,plain,(
% 1.78/0.61    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 1.78/0.61    inference(ennf_transformation,[],[f3])).
% 1.78/0.61  fof(f3,axiom,(
% 1.78/0.61    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).
% 1.78/0.61  fof(f153,plain,(
% 1.78/0.61    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k2_zfmisc_1(X0,k3_tarski(k2_tarski(X1,X2)))) | ~r1_tarski(X3,k2_zfmisc_1(X0,X1))) )),
% 1.78/0.61    inference(superposition,[],[f89,f37])).
% 1.78/0.61  fof(f89,plain,(
% 1.78/0.61    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_tarski(k2_tarski(X1,X0))) | ~r1_tarski(X2,X1)) )),
% 1.78/0.61    inference(superposition,[],[f36,f32])).
% 1.78/0.61  fof(f32,plain,(
% 1.78/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f5])).
% 1.78/0.61  fof(f5,axiom,(
% 1.78/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.78/0.61  % SZS output end Proof for theBenchmark
% 1.78/0.61  % (9006)------------------------------
% 1.78/0.61  % (9006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.61  % (9006)Termination reason: Refutation
% 1.78/0.61  
% 1.78/0.61  % (9006)Memory used [KB]: 2430
% 1.78/0.61  % (9006)Time elapsed: 0.210 s
% 1.78/0.61  % (9006)------------------------------
% 1.78/0.61  % (9006)------------------------------
% 1.78/0.62  % (9028)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.22/0.63  % (9004)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.63  
% 2.22/0.63  % (9004)Memory used [KB]: 6140
% 2.22/0.63  % (9004)Time elapsed: 0.198 s
% 2.22/0.63  % (9004)------------------------------
% 2.22/0.63  % (9004)------------------------------
% 2.22/0.64  % (8998)Success in time 0.3 s
%------------------------------------------------------------------------------
