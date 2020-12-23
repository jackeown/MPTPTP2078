%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:59 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 161 expanded)
%              Number of leaves         :   11 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :   92 ( 238 expanded)
%              Number of equality atoms :   21 ( 110 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f981,plain,(
    $false ),
    inference(subsumption_resolution,[],[f980,f236])).

fof(f236,plain,(
    ! [X0] : r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,X0)),sK3)) ),
    inference(superposition,[],[f202,f46])).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f31,f32,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f202,plain,(
    ! [X2] : r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(X2,X2,sK2)),sK3)) ),
    inference(superposition,[],[f135,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2) = k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f38,f43,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f135,plain,(
    ! [X7] : r1_tarski(sK0,k3_tarski(k1_enumset1(X7,X7,k2_zfmisc_1(sK2,sK3)))) ),
    inference(resolution,[],[f130,f66])).

fof(f66,plain,(
    ! [X8] :
      ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),X8)
      | r1_tarski(sK0,X8) ) ),
    inference(superposition,[],[f57,f54])).

fof(f54,plain,(
    sK0 = k3_xboole_0(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f34,f26])).

fof(f26,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f15,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X1,X0),X2)
      | ~ r1_tarski(X0,X2) ) ),
    inference(superposition,[],[f40,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f130,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0))) ),
    inference(superposition,[],[f45,f46])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f29,f43])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f980,plain,(
    ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3)) ),
    inference(subsumption_resolution,[],[f955,f203])).

fof(f203,plain,(
    ! [X3] : r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(X3,X3,sK4)),sK5)) ),
    inference(superposition,[],[f136,f48])).

fof(f136,plain,(
    ! [X8] : r1_tarski(sK1,k3_tarski(k1_enumset1(X8,X8,k2_zfmisc_1(sK4,sK5)))) ),
    inference(resolution,[],[f130,f67])).

fof(f67,plain,(
    ! [X9] :
      ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),X9)
      | r1_tarski(sK1,X9) ) ),
    inference(superposition,[],[f57,f55])).

fof(f55,plain,(
    sK1 = k3_xboole_0(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f34,f27])).

fof(f27,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f23])).

fof(f955,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK5))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3)) ),
    inference(resolution,[],[f182,f44])).

fof(f44,plain,(
    ~ r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5)))) ),
    inference(definition_unfolding,[],[f28,f43,f43,f43])).

fof(f28,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f23])).

fof(f182,plain,(
    ! [X6,X4,X2,X5,X3] :
      ( r1_tarski(k3_tarski(k1_enumset1(X5,X5,X6)),k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X3,X3,X4))))
      | ~ r1_tarski(X6,k2_zfmisc_1(X2,X4))
      | ~ r1_tarski(X5,k2_zfmisc_1(X2,X3)) ) ),
    inference(superposition,[],[f49,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f39,f43,f43])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f43,f43])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:45:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.19/0.52  % (23383)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.19/0.52  % (23389)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.19/0.52  % (23392)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.19/0.53  % (23400)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.19/0.53  % (23385)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.33/0.53  % (23408)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.33/0.53  % (23384)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.33/0.53  % (23412)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.33/0.53  % (23387)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.33/0.54  % (23388)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.33/0.54  % (23406)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.33/0.54  % (23410)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.33/0.54  % (23386)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.33/0.54  % (23398)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.33/0.54  % (23391)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.33/0.54  % (23411)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.33/0.55  % (23404)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.33/0.55  % (23402)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.33/0.55  % (23390)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.33/0.55  % (23403)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.33/0.55  % (23397)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.33/0.55  % (23396)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.33/0.55  % (23399)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.33/0.55  % (23394)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.33/0.55  % (23395)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.33/0.56  % (23405)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.33/0.56  % (23407)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.33/0.57  % (23401)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.33/0.59  % (23409)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.33/0.60  % (23393)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.33/0.63  % (23389)Refutation found. Thanks to Tanya!
% 1.33/0.63  % SZS status Theorem for theBenchmark
% 1.33/0.63  % SZS output start Proof for theBenchmark
% 2.02/0.63  fof(f981,plain,(
% 2.02/0.63    $false),
% 2.02/0.63    inference(subsumption_resolution,[],[f980,f236])).
% 2.02/0.63  fof(f236,plain,(
% 2.02/0.63    ( ! [X0] : (r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,X0)),sK3))) )),
% 2.02/0.63    inference(superposition,[],[f202,f46])).
% 2.02/0.63  fof(f46,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 2.02/0.63    inference(definition_unfolding,[],[f31,f32,f32])).
% 2.02/0.63  fof(f32,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f9])).
% 2.02/0.63  fof(f9,axiom,(
% 2.02/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.02/0.63  fof(f31,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f8])).
% 2.02/0.63  fof(f8,axiom,(
% 2.02/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.02/0.63  fof(f202,plain,(
% 2.02/0.63    ( ! [X2] : (r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(X2,X2,sK2)),sK3))) )),
% 2.02/0.63    inference(superposition,[],[f135,f48])).
% 2.02/0.63  fof(f48,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k1_enumset1(X0,X0,X1)),X2) = k3_tarski(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 2.02/0.63    inference(definition_unfolding,[],[f38,f43,f43])).
% 2.02/0.63  fof(f43,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.02/0.63    inference(definition_unfolding,[],[f33,f32])).
% 2.02/0.63  fof(f33,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f10])).
% 2.02/0.63  fof(f10,axiom,(
% 2.02/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.02/0.63  fof(f38,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f11])).
% 2.02/0.63  fof(f11,axiom,(
% 2.02/0.63    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 2.02/0.63  fof(f135,plain,(
% 2.02/0.63    ( ! [X7] : (r1_tarski(sK0,k3_tarski(k1_enumset1(X7,X7,k2_zfmisc_1(sK2,sK3))))) )),
% 2.02/0.63    inference(resolution,[],[f130,f66])).
% 2.02/0.63  fof(f66,plain,(
% 2.02/0.63    ( ! [X8] : (~r1_tarski(k2_zfmisc_1(sK2,sK3),X8) | r1_tarski(sK0,X8)) )),
% 2.02/0.63    inference(superposition,[],[f57,f54])).
% 2.02/0.63  fof(f54,plain,(
% 2.02/0.63    sK0 = k3_xboole_0(sK0,k2_zfmisc_1(sK2,sK3))),
% 2.02/0.63    inference(resolution,[],[f34,f26])).
% 2.02/0.63  fof(f26,plain,(
% 2.02/0.63    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 2.02/0.63    inference(cnf_transformation,[],[f23])).
% 2.02/0.65  fof(f23,plain,(
% 2.02/0.65    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 2.02/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f15,f22])).
% 2.02/0.65  fof(f22,plain,(
% 2.02/0.65    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 2.02/0.65    introduced(choice_axiom,[])).
% 2.02/0.65  fof(f15,plain,(
% 2.02/0.65    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 2.02/0.65    inference(flattening,[],[f14])).
% 2.02/0.65  fof(f14,plain,(
% 2.02/0.65    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 2.02/0.65    inference(ennf_transformation,[],[f13])).
% 2.02/0.65  fof(f13,negated_conjecture,(
% 2.02/0.65    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 2.02/0.65    inference(negated_conjecture,[],[f12])).
% 2.02/0.65  fof(f12,conjecture,(
% 2.02/0.65    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 2.02/0.65  fof(f34,plain,(
% 2.02/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.02/0.65    inference(cnf_transformation,[],[f16])).
% 2.02/0.65  fof(f16,plain,(
% 2.02/0.65    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.02/0.65    inference(ennf_transformation,[],[f6])).
% 2.02/0.65  fof(f6,axiom,(
% 2.02/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.02/0.65  fof(f57,plain,(
% 2.02/0.65    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X2) | ~r1_tarski(X0,X2)) )),
% 2.02/0.65    inference(superposition,[],[f40,f30])).
% 2.02/0.65  fof(f30,plain,(
% 2.02/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f1])).
% 2.02/0.65  fof(f1,axiom,(
% 2.02/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.02/0.65  fof(f40,plain,(
% 2.02/0.65    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f17])).
% 2.02/0.65  fof(f17,plain,(
% 2.02/0.65    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 2.02/0.65    inference(ennf_transformation,[],[f3])).
% 2.02/0.65  fof(f3,axiom,(
% 2.02/0.65    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 2.02/0.65  fof(f130,plain,(
% 2.02/0.65    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0)))) )),
% 2.02/0.65    inference(superposition,[],[f45,f46])).
% 2.02/0.65  fof(f45,plain,(
% 2.02/0.65    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 2.02/0.65    inference(definition_unfolding,[],[f29,f43])).
% 2.02/0.65  fof(f29,plain,(
% 2.02/0.65    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.02/0.65    inference(cnf_transformation,[],[f7])).
% 2.02/0.65  fof(f7,axiom,(
% 2.02/0.65    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.02/0.65  fof(f980,plain,(
% 2.02/0.65    ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3))),
% 2.02/0.65    inference(subsumption_resolution,[],[f955,f203])).
% 2.02/0.65  fof(f203,plain,(
% 2.02/0.65    ( ! [X3] : (r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(X3,X3,sK4)),sK5))) )),
% 2.02/0.65    inference(superposition,[],[f136,f48])).
% 2.02/0.65  fof(f136,plain,(
% 2.02/0.65    ( ! [X8] : (r1_tarski(sK1,k3_tarski(k1_enumset1(X8,X8,k2_zfmisc_1(sK4,sK5))))) )),
% 2.02/0.65    inference(resolution,[],[f130,f67])).
% 2.02/0.65  fof(f67,plain,(
% 2.02/0.65    ( ! [X9] : (~r1_tarski(k2_zfmisc_1(sK4,sK5),X9) | r1_tarski(sK1,X9)) )),
% 2.02/0.65    inference(superposition,[],[f57,f55])).
% 2.02/0.65  fof(f55,plain,(
% 2.02/0.65    sK1 = k3_xboole_0(sK1,k2_zfmisc_1(sK4,sK5))),
% 2.02/0.65    inference(resolution,[],[f34,f27])).
% 2.02/0.65  fof(f27,plain,(
% 2.02/0.65    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 2.02/0.65    inference(cnf_transformation,[],[f23])).
% 2.02/0.65  fof(f955,plain,(
% 2.02/0.65    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK5)) | ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),sK3))),
% 2.02/0.65    inference(resolution,[],[f182,f44])).
% 2.02/0.65  fof(f44,plain,(
% 2.02/0.65    ~r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k1_enumset1(sK2,sK2,sK4)),k3_tarski(k1_enumset1(sK3,sK3,sK5))))),
% 2.02/0.65    inference(definition_unfolding,[],[f28,f43,f43,f43])).
% 2.02/0.65  fof(f28,plain,(
% 2.02/0.65    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 2.02/0.65    inference(cnf_transformation,[],[f23])).
% 2.02/0.65  fof(f182,plain,(
% 2.02/0.65    ( ! [X6,X4,X2,X5,X3] : (r1_tarski(k3_tarski(k1_enumset1(X5,X5,X6)),k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X3,X3,X4)))) | ~r1_tarski(X6,k2_zfmisc_1(X2,X4)) | ~r1_tarski(X5,k2_zfmisc_1(X2,X3))) )),
% 2.02/0.65    inference(superposition,[],[f49,f47])).
% 2.02/0.65  fof(f47,plain,(
% 2.02/0.65    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 2.02/0.65    inference(definition_unfolding,[],[f39,f43,f43])).
% 2.02/0.65  fof(f39,plain,(
% 2.02/0.65    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 2.02/0.65    inference(cnf_transformation,[],[f11])).
% 2.02/0.65  fof(f49,plain,(
% 2.02/0.65    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),k3_tarski(k1_enumset1(X1,X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 2.02/0.65    inference(definition_unfolding,[],[f42,f43,f43])).
% 2.02/0.65  fof(f42,plain,(
% 2.02/0.65    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 2.02/0.65    inference(cnf_transformation,[],[f21])).
% 2.02/0.65  fof(f21,plain,(
% 2.02/0.65    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 2.02/0.65    inference(flattening,[],[f20])).
% 2.02/0.65  fof(f20,plain,(
% 2.02/0.65    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 2.02/0.65    inference(ennf_transformation,[],[f4])).
% 2.02/0.65  fof(f4,axiom,(
% 2.02/0.65    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 2.02/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).
% 2.02/0.65  % SZS output end Proof for theBenchmark
% 2.02/0.65  % (23389)------------------------------
% 2.02/0.65  % (23389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.65  % (23389)Termination reason: Refutation
% 2.02/0.65  
% 2.02/0.65  % (23389)Memory used [KB]: 11769
% 2.02/0.65  % (23389)Time elapsed: 0.214 s
% 2.02/0.65  % (23389)------------------------------
% 2.02/0.65  % (23389)------------------------------
% 2.02/0.65  % (23382)Success in time 0.286 s
%------------------------------------------------------------------------------
