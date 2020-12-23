%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 115 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 215 expanded)
%              Number of equality atoms :   20 (  62 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f572,plain,(
    $false ),
    inference(subsumption_resolution,[],[f571,f120])).

fof(f120,plain,(
    ! [X2] : r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,X2)),sK3)) ),
    inference(superposition,[],[f80,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f31,f26,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f80,plain,(
    ! [X0] : r1_tarski(sK0,k3_tarski(k2_tarski(k2_zfmisc_1(sK2,sK3),X0))) ),
    inference(resolution,[],[f78,f71])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(resolution,[],[f41,f43])).

fof(f43,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
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

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f34,f26])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f78,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),X0)
      | r1_tarski(sK0,X0) ) ),
    inference(superposition,[],[f41,f69])).

fof(f69,plain,(
    k2_zfmisc_1(sK2,sK3) = k3_tarski(k2_tarski(sK0,k2_zfmisc_1(sK2,sK3))) ),
    inference(resolution,[],[f37,f22])).

fof(f22,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k2_tarski(X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f571,plain,(
    ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK3)) ),
    inference(subsumption_resolution,[],[f552,f378])).

fof(f378,plain,(
    ! [X2] : r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(X2,sK4)),sK5)) ),
    inference(superposition,[],[f332,f39])).

fof(f332,plain,(
    ! [X14] : r1_tarski(sK1,k3_tarski(k2_tarski(X14,k2_zfmisc_1(sK4,sK5)))) ),
    inference(superposition,[],[f279,f70])).

fof(f70,plain,(
    k2_zfmisc_1(sK4,sK5) = k3_tarski(k2_tarski(sK1,k2_zfmisc_1(sK4,sK5))) ),
    inference(resolution,[],[f37,f23])).

fof(f23,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f19])).

fof(f279,plain,(
    ! [X2,X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X2))))) ),
    inference(resolution,[],[f89,f25])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f89,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X8,X9)),X10),X11)
      | r1_tarski(X8,k3_tarski(k2_tarski(X10,X11))) ) ),
    inference(resolution,[],[f40,f41])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f33,f26])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f552,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK5))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK3)) ),
    inference(resolution,[],[f148,f36])).

fof(f36,plain,(
    ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(definition_unfolding,[],[f24,f26,f26,f26])).

fof(f24,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f19])).

fof(f148,plain,(
    ! [X10,X8,X7,X11,X9] :
      ( r1_tarski(k3_tarski(k2_tarski(X10,X11)),k2_zfmisc_1(X7,k3_tarski(k2_tarski(X8,X9))))
      | ~ r1_tarski(X11,k2_zfmisc_1(X7,X9))
      | ~ r1_tarski(X10,k2_zfmisc_1(X7,X8)) ) ),
    inference(superposition,[],[f42,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f32,f26,f26])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f26,f26])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:10:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (384)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (385)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.51  % (400)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (391)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (394)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.51  % (388)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (402)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.52  % (408)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (402)Refutation not found, incomplete strategy% (402)------------------------------
% 0.22/0.52  % (402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (398)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (410)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (386)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (417)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (402)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (402)Memory used [KB]: 10618
% 0.22/0.52  % (402)Time elapsed: 0.106 s
% 0.22/0.52  % (402)------------------------------
% 0.22/0.52  % (402)------------------------------
% 0.22/0.52  % (413)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (401)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (396)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (405)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (399)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (389)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (407)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (403)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (412)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (415)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (392)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (416)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (404)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (390)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (411)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (416)Refutation not found, incomplete strategy% (416)------------------------------
% 0.22/0.54  % (416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (416)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (416)Memory used [KB]: 10746
% 0.22/0.54  % (416)Time elapsed: 0.140 s
% 0.22/0.54  % (416)------------------------------
% 0.22/0.54  % (416)------------------------------
% 0.22/0.55  % (393)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (395)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (395)Refutation not found, incomplete strategy% (395)------------------------------
% 0.22/0.55  % (395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (395)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (395)Memory used [KB]: 10746
% 0.22/0.55  % (395)Time elapsed: 0.151 s
% 0.22/0.55  % (395)------------------------------
% 0.22/0.55  % (395)------------------------------
% 0.22/0.56  % (406)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.57  % (391)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f572,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(subsumption_resolution,[],[f571,f120])).
% 0.22/0.57  fof(f120,plain,(
% 0.22/0.57    ( ! [X2] : (r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,X2)),sK3))) )),
% 0.22/0.57    inference(superposition,[],[f80,f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.57    inference(definition_unfolding,[],[f31,f26,f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 0.22/0.57  fof(f80,plain,(
% 0.22/0.57    ( ! [X0] : (r1_tarski(sK0,k3_tarski(k2_tarski(k2_zfmisc_1(sK2,sK3),X0)))) )),
% 0.22/0.57    inference(resolution,[],[f78,f71])).
% 0.22/0.57  fof(f71,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 0.22/0.57    inference(resolution,[],[f41,f43])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.57    inference(equality_resolution,[],[f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.57    inference(flattening,[],[f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.57    inference(nnf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f34,f26])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.57    inference(ennf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.57  fof(f78,plain,(
% 0.22/0.57    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK2,sK3),X0) | r1_tarski(sK0,X0)) )),
% 0.22/0.57    inference(superposition,[],[f41,f69])).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    k2_zfmisc_1(sK2,sK3) = k3_tarski(k2_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 0.22/0.57    inference(resolution,[],[f37,f22])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f12,plain,(
% 0.22/0.57    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 0.22/0.57    inference(flattening,[],[f11])).
% 0.22/0.57  fof(f11,plain,(
% 0.22/0.57    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 0.22/0.57    inference(negated_conjecture,[],[f9])).
% 0.22/0.57  fof(f9,conjecture,(
% 0.22/0.57    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1) )),
% 0.22/0.57    inference(definition_unfolding,[],[f27,f26])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,plain,(
% 0.22/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.57  fof(f571,plain,(
% 0.22/0.57    ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK3))),
% 0.22/0.57    inference(subsumption_resolution,[],[f552,f378])).
% 0.22/0.57  fof(f378,plain,(
% 0.22/0.57    ( ! [X2] : (r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(X2,sK4)),sK5))) )),
% 0.22/0.57    inference(superposition,[],[f332,f39])).
% 0.22/0.57  fof(f332,plain,(
% 0.22/0.57    ( ! [X14] : (r1_tarski(sK1,k3_tarski(k2_tarski(X14,k2_zfmisc_1(sK4,sK5))))) )),
% 0.22/0.57    inference(superposition,[],[f279,f70])).
% 0.22/0.57  fof(f70,plain,(
% 0.22/0.57    k2_zfmisc_1(sK4,sK5) = k3_tarski(k2_tarski(sK1,k2_zfmisc_1(sK4,sK5)))),
% 0.22/0.57    inference(resolution,[],[f37,f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f279,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X2)))))) )),
% 0.22/0.57    inference(resolution,[],[f89,f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.57  fof(f89,plain,(
% 0.22/0.57    ( ! [X10,X8,X11,X9] : (~r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X8,X9)),X10),X11) | r1_tarski(X8,k3_tarski(k2_tarski(X10,X11)))) )),
% 0.22/0.57    inference(resolution,[],[f40,f41])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f33,f26])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.57    inference(ennf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.22/0.57  fof(f552,plain,(
% 0.22/0.57    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK5)) | ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK3))),
% 0.22/0.57    inference(resolution,[],[f148,f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ~r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))),
% 0.22/0.57    inference(definition_unfolding,[],[f24,f26,f26,f26])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f148,plain,(
% 0.22/0.57    ( ! [X10,X8,X7,X11,X9] : (r1_tarski(k3_tarski(k2_tarski(X10,X11)),k2_zfmisc_1(X7,k3_tarski(k2_tarski(X8,X9)))) | ~r1_tarski(X11,k2_zfmisc_1(X7,X9)) | ~r1_tarski(X10,k2_zfmisc_1(X7,X8))) )),
% 0.22/0.57    inference(superposition,[],[f42,f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 0.22/0.57    inference(definition_unfolding,[],[f32,f26,f26])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f8])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f35,f26,f26])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.22/0.57    inference(flattening,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (391)------------------------------
% 0.22/0.57  % (391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (391)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (391)Memory used [KB]: 11385
% 0.22/0.57  % (391)Time elapsed: 0.166 s
% 0.22/0.57  % (391)------------------------------
% 0.22/0.57  % (391)------------------------------
% 0.22/0.57  % (380)Success in time 0.205 s
%------------------------------------------------------------------------------
