%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 131 expanded)
%              Number of leaves         :   10 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :   99 ( 242 expanded)
%              Number of equality atoms :   29 (  99 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f949,plain,(
    $false ),
    inference(resolution,[],[f943,f753])).

fof(f753,plain,(
    ~ r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(subsumption_resolution,[],[f733,f322])).

fof(f322,plain,(
    ! [X0] : r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,X0)))) ),
    inference(superposition,[],[f295,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f36,f27,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f295,plain,(
    ! [X16] : r1_tarski(sK0,k3_tarski(k2_tarski(k2_zfmisc_1(sK2,sK3),X16))) ),
    inference(subsumption_resolution,[],[f281,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f33,f25])).

fof(f25,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f281,plain,(
    ! [X16] :
      ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,X16)
      | r1_tarski(sK0,k3_tarski(k2_tarski(k2_zfmisc_1(sK2,sK3),X16))) ) ),
    inference(superposition,[],[f112,f49])).

fof(f49,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f33,f22])).

fof(f22,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f13,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f112,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(X3,X4),X5)
      | r1_tarski(X3,k3_tarski(k2_tarski(X4,X5))) ) ),
    inference(superposition,[],[f32,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k2_tarski(X1,X2))) ),
    inference(definition_unfolding,[],[f34,f27])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f733,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5))))
    | ~ r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(resolution,[],[f223,f38])).

fof(f38,plain,(
    ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(definition_unfolding,[],[f24,f27,f27,f27])).

fof(f24,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f18])).

fof(f223,plain,(
    ! [X23,X21,X19,X22,X20] :
      ( r1_tarski(k3_tarski(k2_tarski(X22,X23)),k2_zfmisc_1(k3_tarski(k2_tarski(X19,X21)),X20))
      | ~ r1_tarski(X23,k2_zfmisc_1(X21,X20))
      | ~ r1_tarski(X22,k2_zfmisc_1(X19,X20)) ) ),
    inference(superposition,[],[f43,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f35,f27,f27])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f27,f27])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f943,plain,(
    ! [X0] : r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(X0,sK5)))) ),
    inference(superposition,[],[f857,f41])).

fof(f857,plain,(
    ! [X0] : r1_tarski(sK1,k3_tarski(k2_tarski(X0,k2_zfmisc_1(sK4,sK5)))) ),
    inference(trivial_inequality_removal,[],[f838])).

fof(f838,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(sK1,k3_tarski(k2_tarski(X0,k2_zfmisc_1(sK4,sK5)))) ) ),
    inference(superposition,[],[f112,f691])).

fof(f691,plain,(
    ! [X8] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,X8),k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f648,f33])).

fof(f648,plain,(
    ! [X8] : r1_tarski(k4_xboole_0(sK1,X8),k2_zfmisc_1(sK4,sK5)) ),
    inference(superposition,[],[f293,f88])).

fof(f88,plain,(
    k2_zfmisc_1(sK4,sK5) = k3_tarski(k2_tarski(sK1,k2_zfmisc_1(sK4,sK5))) ),
    inference(resolution,[],[f39,f23])).

fof(f23,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k2_tarski(X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f293,plain,(
    ! [X6,X4,X5] : r1_tarski(k4_xboole_0(X4,X5),k3_tarski(k2_tarski(X4,X6))) ),
    inference(subsumption_resolution,[],[f277,f46])).

fof(f277,plain,(
    ! [X6,X4,X5] :
      ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,X6)
      | r1_tarski(k4_xboole_0(X4,X5),k3_tarski(k2_tarski(X4,X6))) ) ),
    inference(superposition,[],[f112,f48])).

fof(f48,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(resolution,[],[f33,f26])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:22:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (14408)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (14405)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (14417)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.51  % (14418)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.51  % (14416)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (14409)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (14421)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.52  % (14411)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (14402)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (14403)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (14424)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (14415)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (14425)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (14419)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (14413)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (14406)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (14407)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (14404)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (14418)Refutation not found, incomplete strategy% (14418)------------------------------
% 0.22/0.53  % (14418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (14418)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (14418)Memory used [KB]: 10618
% 0.22/0.53  % (14418)Time elapsed: 0.120 s
% 0.22/0.53  % (14418)------------------------------
% 0.22/0.53  % (14418)------------------------------
% 0.22/0.54  % (14420)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (14430)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (14431)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (14423)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (14422)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (14412)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (14426)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (14428)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (14414)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (14410)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (14431)Refutation not found, incomplete strategy% (14431)------------------------------
% 0.22/0.55  % (14431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (14431)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (14431)Memory used [KB]: 1663
% 0.22/0.55  % (14431)Time elapsed: 0.003 s
% 0.22/0.55  % (14431)------------------------------
% 0.22/0.55  % (14431)------------------------------
% 0.22/0.56  % (14412)Refutation not found, incomplete strategy% (14412)------------------------------
% 0.22/0.56  % (14412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (14412)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (14412)Memory used [KB]: 10746
% 0.22/0.56  % (14412)Time elapsed: 0.150 s
% 0.22/0.56  % (14412)------------------------------
% 0.22/0.56  % (14412)------------------------------
% 0.22/0.56  % (14429)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  % (14427)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.57  % (14430)Refutation not found, incomplete strategy% (14430)------------------------------
% 0.22/0.57  % (14430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (14430)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (14430)Memory used [KB]: 10746
% 0.22/0.57  % (14430)Time elapsed: 0.158 s
% 0.22/0.57  % (14430)------------------------------
% 0.22/0.57  % (14430)------------------------------
% 0.22/0.57  % (14408)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 1.66/0.59  % SZS output start Proof for theBenchmark
% 1.66/0.59  fof(f949,plain,(
% 1.66/0.59    $false),
% 1.66/0.59    inference(resolution,[],[f943,f753])).
% 1.66/0.59  fof(f753,plain,(
% 1.66/0.59    ~r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5))))),
% 1.66/0.59    inference(subsumption_resolution,[],[f733,f322])).
% 1.66/0.59  fof(f322,plain,(
% 1.66/0.59    ( ! [X0] : (r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,X0))))) )),
% 1.66/0.59    inference(superposition,[],[f295,f41])).
% 1.66/0.59  fof(f41,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 1.66/0.59    inference(definition_unfolding,[],[f36,f27,f27])).
% 1.66/0.59  fof(f27,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.66/0.59    inference(cnf_transformation,[],[f8])).
% 1.66/0.59  fof(f8,axiom,(
% 1.66/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.66/0.59  fof(f36,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 1.66/0.59    inference(cnf_transformation,[],[f9])).
% 1.66/0.59  fof(f9,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 1.66/0.59  fof(f295,plain,(
% 1.66/0.59    ( ! [X16] : (r1_tarski(sK0,k3_tarski(k2_tarski(k2_zfmisc_1(sK2,sK3),X16)))) )),
% 1.66/0.59    inference(subsumption_resolution,[],[f281,f46])).
% 1.66/0.59  fof(f46,plain,(
% 1.66/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.66/0.59    inference(resolution,[],[f33,f25])).
% 1.66/0.59  fof(f25,plain,(
% 1.66/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f5])).
% 1.66/0.59  fof(f5,axiom,(
% 1.66/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.66/0.59  fof(f33,plain,(
% 1.66/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.66/0.59    inference(cnf_transformation,[],[f21])).
% 1.66/0.59  fof(f21,plain,(
% 1.66/0.59    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.66/0.59    inference(nnf_transformation,[],[f2])).
% 1.66/0.59  fof(f2,axiom,(
% 1.66/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.66/0.59  fof(f281,plain,(
% 1.66/0.59    ( ! [X16] : (k1_xboole_0 != k4_xboole_0(k1_xboole_0,X16) | r1_tarski(sK0,k3_tarski(k2_tarski(k2_zfmisc_1(sK2,sK3),X16)))) )),
% 1.66/0.59    inference(superposition,[],[f112,f49])).
% 1.66/0.59  fof(f49,plain,(
% 1.66/0.59    k1_xboole_0 = k4_xboole_0(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.66/0.59    inference(resolution,[],[f33,f22])).
% 1.66/0.59  fof(f22,plain,(
% 1.66/0.59    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.66/0.59    inference(cnf_transformation,[],[f18])).
% 1.66/0.59  fof(f18,plain,(
% 1.66/0.59    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 1.66/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f13,f17])).
% 1.66/0.59  fof(f17,plain,(
% 1.66/0.59    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 1.66/0.59    introduced(choice_axiom,[])).
% 1.66/0.59  fof(f13,plain,(
% 1.66/0.59    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 1.66/0.59    inference(flattening,[],[f12])).
% 1.66/0.59  fof(f12,plain,(
% 1.66/0.59    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 1.66/0.59    inference(ennf_transformation,[],[f11])).
% 1.66/0.59  fof(f11,negated_conjecture,(
% 1.66/0.59    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 1.66/0.59    inference(negated_conjecture,[],[f10])).
% 1.66/0.59  fof(f10,conjecture,(
% 1.66/0.59    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 1.66/0.59  fof(f112,plain,(
% 1.66/0.59    ( ! [X4,X5,X3] : (k1_xboole_0 != k4_xboole_0(k4_xboole_0(X3,X4),X5) | r1_tarski(X3,k3_tarski(k2_tarski(X4,X5)))) )),
% 1.66/0.59    inference(superposition,[],[f32,f40])).
% 1.66/0.59  fof(f40,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 1.66/0.59    inference(definition_unfolding,[],[f34,f27])).
% 1.66/0.59  fof(f34,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.66/0.59    inference(cnf_transformation,[],[f7])).
% 1.66/0.59  fof(f7,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.66/0.59  fof(f32,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f21])).
% 1.66/0.59  fof(f733,plain,(
% 1.66/0.59    ~r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(sK3,sK5)))) | ~r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k2_tarski(sK3,sK5))))),
% 1.66/0.59    inference(resolution,[],[f223,f38])).
% 1.66/0.59  fof(f38,plain,(
% 1.66/0.59    ~r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))),
% 1.66/0.59    inference(definition_unfolding,[],[f24,f27,f27,f27])).
% 1.66/0.59  fof(f24,plain,(
% 1.66/0.59    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 1.66/0.59    inference(cnf_transformation,[],[f18])).
% 1.66/0.59  fof(f223,plain,(
% 1.66/0.59    ( ! [X23,X21,X19,X22,X20] : (r1_tarski(k3_tarski(k2_tarski(X22,X23)),k2_zfmisc_1(k3_tarski(k2_tarski(X19,X21)),X20)) | ~r1_tarski(X23,k2_zfmisc_1(X21,X20)) | ~r1_tarski(X22,k2_zfmisc_1(X19,X20))) )),
% 1.66/0.59    inference(superposition,[],[f43,f42])).
% 1.66/0.59  fof(f42,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 1.66/0.59    inference(definition_unfolding,[],[f35,f27,f27])).
% 1.66/0.59  fof(f35,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 1.66/0.59    inference(cnf_transformation,[],[f9])).
% 1.66/0.59  fof(f43,plain,(
% 1.66/0.59    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.66/0.59    inference(definition_unfolding,[],[f37,f27,f27])).
% 1.66/0.59  fof(f37,plain,(
% 1.66/0.59    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f16])).
% 1.66/0.59  fof(f16,plain,(
% 1.66/0.59    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 1.66/0.59    inference(flattening,[],[f15])).
% 1.66/0.59  fof(f15,plain,(
% 1.66/0.59    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 1.66/0.59    inference(ennf_transformation,[],[f4])).
% 1.66/0.59  fof(f4,axiom,(
% 1.66/0.59    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).
% 1.66/0.59  fof(f943,plain,(
% 1.66/0.59    ( ! [X0] : (r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k2_tarski(X0,sK5))))) )),
% 1.66/0.59    inference(superposition,[],[f857,f41])).
% 1.66/0.59  fof(f857,plain,(
% 1.66/0.59    ( ! [X0] : (r1_tarski(sK1,k3_tarski(k2_tarski(X0,k2_zfmisc_1(sK4,sK5))))) )),
% 1.66/0.59    inference(trivial_inequality_removal,[],[f838])).
% 1.66/0.59  fof(f838,plain,(
% 1.66/0.59    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,k3_tarski(k2_tarski(X0,k2_zfmisc_1(sK4,sK5))))) )),
% 1.66/0.59    inference(superposition,[],[f112,f691])).
% 1.66/0.59  fof(f691,plain,(
% 1.66/0.59    ( ! [X8] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,X8),k2_zfmisc_1(sK4,sK5))) )),
% 1.66/0.59    inference(resolution,[],[f648,f33])).
% 1.66/0.59  fof(f648,plain,(
% 1.66/0.59    ( ! [X8] : (r1_tarski(k4_xboole_0(sK1,X8),k2_zfmisc_1(sK4,sK5))) )),
% 1.66/0.59    inference(superposition,[],[f293,f88])).
% 1.66/0.59  fof(f88,plain,(
% 1.66/0.59    k2_zfmisc_1(sK4,sK5) = k3_tarski(k2_tarski(sK1,k2_zfmisc_1(sK4,sK5)))),
% 1.66/0.59    inference(resolution,[],[f39,f23])).
% 1.66/0.59  fof(f23,plain,(
% 1.66/0.59    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 1.66/0.59    inference(cnf_transformation,[],[f18])).
% 1.66/0.59  fof(f39,plain,(
% 1.66/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1) )),
% 1.66/0.59    inference(definition_unfolding,[],[f28,f27])).
% 1.66/0.59  fof(f28,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f14])).
% 1.66/0.59  fof(f14,plain,(
% 1.66/0.59    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.66/0.59    inference(ennf_transformation,[],[f3])).
% 1.66/0.59  fof(f3,axiom,(
% 1.66/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.66/0.59  fof(f293,plain,(
% 1.66/0.59    ( ! [X6,X4,X5] : (r1_tarski(k4_xboole_0(X4,X5),k3_tarski(k2_tarski(X4,X6)))) )),
% 1.66/0.59    inference(subsumption_resolution,[],[f277,f46])).
% 1.66/0.59  fof(f277,plain,(
% 1.66/0.59    ( ! [X6,X4,X5] : (k1_xboole_0 != k4_xboole_0(k1_xboole_0,X6) | r1_tarski(k4_xboole_0(X4,X5),k3_tarski(k2_tarski(X4,X6)))) )),
% 1.66/0.59    inference(superposition,[],[f112,f48])).
% 1.66/0.59  fof(f48,plain,(
% 1.66/0.59    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 1.66/0.59    inference(resolution,[],[f33,f26])).
% 1.66/0.59  fof(f26,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f6])).
% 1.66/0.59  fof(f6,axiom,(
% 1.66/0.59    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.66/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.84/0.59  % SZS output end Proof for theBenchmark
% 1.84/0.59  % (14408)------------------------------
% 1.84/0.59  % (14408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.59  % (14408)Termination reason: Refutation
% 1.84/0.59  
% 1.84/0.59  % (14408)Memory used [KB]: 11513
% 1.84/0.59  % (14408)Time elapsed: 0.140 s
% 1.84/0.59  % (14408)------------------------------
% 1.84/0.59  % (14408)------------------------------
% 1.84/0.60  % (14401)Success in time 0.232 s
%------------------------------------------------------------------------------
