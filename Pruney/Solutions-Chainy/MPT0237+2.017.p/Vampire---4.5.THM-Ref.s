%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:31 EST 2020

% Result     : Theorem 1.88s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 100 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :   18
%              Number of atoms          :  144 ( 188 expanded)
%              Number of equality atoms :   80 ( 108 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(resolution,[],[f231,f73])).

fof(f73,plain,(
    ! [X0] : r1_tarski(X0,k3_tarski(k1_tarski(X0))) ),
    inference(superposition,[],[f41,f71])).

fof(f71,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) ),
    inference(superposition,[],[f44,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f231,plain,(
    ! [X0] : ~ r1_tarski(k1_tarski(sK0),X0) ),
    inference(resolution,[],[f208,f79])).

fof(f79,plain,(
    ! [X6,X7] :
      ( r1_tarski(X6,X6)
      | ~ r1_tarski(X6,X7) ) ),
    inference(superposition,[],[f42,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f208,plain,(
    ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f205,f38])).

fof(f38,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f205,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0))
    | ~ r1_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f204])).

fof(f204,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0))
    | ~ r1_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    inference(superposition,[],[f202,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f202,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_xboole_0)
    | ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f190,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = k4_xboole_0(X1,k1_xboole_0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(backward_demodulation,[],[f85,f126])).

fof(f126,plain,(
    ! [X3] : k4_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f47,f107])).

fof(f107,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(X3,k1_xboole_0) ),
    inference(resolution,[],[f101,f66])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f42,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f101,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f82,f38])).

fof(f82,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ r1_tarski(X2,X3)
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f57,f51])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = k5_xboole_0(X1,k1_xboole_0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f46,f57])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f190,plain,(
    k1_tarski(sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f186,f40])).

fof(f186,plain,(
    k2_tarski(sK0,sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f72,f184])).

fof(f184,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f183,f65])).

fof(f65,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f183,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f161,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f161,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f160])).

fof(f160,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | sK0 = sK1 ),
    inference(superposition,[],[f159,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f159,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f72,f86])).

fof(f86,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,X2) = k5_xboole_0(X3,X2)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f46,f51])).

fof(f72,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(superposition,[],[f37,f44])).

fof(f37,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f30])).

fof(f30,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:26:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (13157)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (13150)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (13157)Refutation not found, incomplete strategy% (13157)------------------------------
% 0.22/0.55  % (13157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (13149)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.56  % (13157)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (13157)Memory used [KB]: 6524
% 0.22/0.56  % (13157)Time elapsed: 0.129 s
% 0.22/0.56  % (13157)------------------------------
% 0.22/0.56  % (13157)------------------------------
% 0.22/0.56  % (13161)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.57  % (13151)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.57  % (13148)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.57  % (13165)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.57  % (13166)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.57  % (13146)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.57  % (13147)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.58  % (13169)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.53/0.59  % (13158)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.53/0.59  % (13152)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.53/0.59  % (13153)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.53/0.59  % (13158)Refutation not found, incomplete strategy% (13158)------------------------------
% 1.53/0.59  % (13158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.60  % (13147)Refutation not found, incomplete strategy% (13147)------------------------------
% 1.53/0.60  % (13147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.60  % (13147)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.60  
% 1.53/0.60  % (13147)Memory used [KB]: 1663
% 1.53/0.60  % (13147)Time elapsed: 0.147 s
% 1.53/0.60  % (13147)------------------------------
% 1.53/0.60  % (13147)------------------------------
% 1.53/0.60  % (13158)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.60  
% 1.53/0.60  % (13158)Memory used [KB]: 10618
% 1.53/0.60  % (13158)Time elapsed: 0.157 s
% 1.53/0.60  % (13158)------------------------------
% 1.53/0.60  % (13158)------------------------------
% 1.53/0.60  % (13168)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.88/0.60  % (13175)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.88/0.60  % (13154)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.88/0.60  % (13167)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.88/0.60  % (13164)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.88/0.60  % (13173)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.88/0.61  % (13172)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.88/0.61  % (13159)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.88/0.61  % (13156)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.88/0.61  % (13162)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.88/0.61  % (13155)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.88/0.61  % (13160)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.88/0.61  % (13170)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.88/0.61  % (13171)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.88/0.61  % (13164)Refutation not found, incomplete strategy% (13164)------------------------------
% 1.88/0.61  % (13164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.61  % (13173)Refutation not found, incomplete strategy% (13173)------------------------------
% 1.88/0.61  % (13173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.61  % (13162)Refutation not found, incomplete strategy% (13162)------------------------------
% 1.88/0.61  % (13162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.61  % (13164)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.61  
% 1.88/0.61  % (13164)Memory used [KB]: 1663
% 1.88/0.61  % (13164)Time elapsed: 0.193 s
% 1.88/0.61  % (13164)------------------------------
% 1.88/0.61  % (13164)------------------------------
% 1.88/0.61  % (13175)Refutation not found, incomplete strategy% (13175)------------------------------
% 1.88/0.61  % (13175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.61  % (13175)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.61  
% 1.88/0.61  % (13175)Memory used [KB]: 1663
% 1.88/0.61  % (13175)Time elapsed: 0.003 s
% 1.88/0.61  % (13175)------------------------------
% 1.88/0.61  % (13175)------------------------------
% 1.88/0.61  % (13163)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.88/0.61  % (13163)Refutation not found, incomplete strategy% (13163)------------------------------
% 1.88/0.61  % (13163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.61  % (13173)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.61  
% 1.88/0.61  % (13173)Memory used [KB]: 6140
% 1.88/0.61  % (13173)Time elapsed: 0.192 s
% 1.88/0.61  % (13173)------------------------------
% 1.88/0.61  % (13173)------------------------------
% 1.88/0.62  % (13160)Refutation not found, incomplete strategy% (13160)------------------------------
% 1.88/0.62  % (13160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.62  % (13160)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.62  
% 1.88/0.62  % (13160)Memory used [KB]: 1663
% 1.88/0.62  % (13160)Time elapsed: 0.191 s
% 1.88/0.62  % (13160)------------------------------
% 1.88/0.62  % (13160)------------------------------
% 1.88/0.62  % (13155)Refutation found. Thanks to Tanya!
% 1.88/0.62  % SZS status Theorem for theBenchmark
% 1.88/0.62  % (13172)Refutation not found, incomplete strategy% (13172)------------------------------
% 1.88/0.62  % (13172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.62  % (13171)Refutation not found, incomplete strategy% (13171)------------------------------
% 1.88/0.62  % (13171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.62  % (13163)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.62  
% 1.88/0.62  % (13163)Memory used [KB]: 1663
% 1.88/0.62  % (13163)Time elapsed: 0.189 s
% 1.88/0.62  % (13163)------------------------------
% 1.88/0.62  % (13163)------------------------------
% 1.88/0.62  % (13171)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.62  
% 1.88/0.62  % (13171)Memory used [KB]: 6140
% 1.88/0.62  % (13171)Time elapsed: 0.200 s
% 1.88/0.62  % (13171)------------------------------
% 1.88/0.62  % (13171)------------------------------
% 1.88/0.62  % (13170)Refutation not found, incomplete strategy% (13170)------------------------------
% 1.88/0.62  % (13170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.62  % (13162)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.62  
% 1.88/0.62  % (13162)Memory used [KB]: 10618
% 1.88/0.62  % (13162)Time elapsed: 0.191 s
% 1.88/0.62  % (13162)------------------------------
% 1.88/0.62  % (13162)------------------------------
% 1.88/0.63  % (13170)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.63  
% 1.88/0.63  % (13170)Memory used [KB]: 10618
% 1.88/0.63  % (13170)Time elapsed: 0.199 s
% 1.88/0.63  % (13170)------------------------------
% 1.88/0.63  % (13170)------------------------------
% 1.88/0.63  % (13172)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.63  
% 1.88/0.63  % (13172)Memory used [KB]: 6140
% 1.88/0.63  % (13172)Time elapsed: 0.203 s
% 1.88/0.63  % (13172)------------------------------
% 1.88/0.63  % (13172)------------------------------
% 1.88/0.63  % (13174)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.88/0.63  % SZS output start Proof for theBenchmark
% 1.88/0.63  fof(f241,plain,(
% 1.88/0.63    $false),
% 1.88/0.63    inference(resolution,[],[f231,f73])).
% 1.88/0.63  fof(f73,plain,(
% 1.88/0.63    ( ! [X0] : (r1_tarski(X0,k3_tarski(k1_tarski(X0)))) )),
% 1.88/0.63    inference(superposition,[],[f41,f71])).
% 1.88/0.63  fof(f71,plain,(
% 1.88/0.63    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))) )),
% 1.88/0.63    inference(superposition,[],[f44,f40])).
% 1.88/0.63  fof(f40,plain,(
% 1.88/0.63    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.88/0.63    inference(cnf_transformation,[],[f12])).
% 1.88/0.63  fof(f12,axiom,(
% 1.88/0.63    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.88/0.63  fof(f44,plain,(
% 1.88/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.88/0.63    inference(cnf_transformation,[],[f20])).
% 1.88/0.63  fof(f20,axiom,(
% 1.88/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.88/0.63  fof(f41,plain,(
% 1.88/0.63    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.88/0.63    inference(cnf_transformation,[],[f8])).
% 1.88/0.63  fof(f8,axiom,(
% 1.88/0.63    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.88/0.63  fof(f231,plain,(
% 1.88/0.63    ( ! [X0] : (~r1_tarski(k1_tarski(sK0),X0)) )),
% 1.88/0.63    inference(resolution,[],[f208,f79])).
% 1.88/0.63  fof(f79,plain,(
% 1.88/0.63    ( ! [X6,X7] : (r1_tarski(X6,X6) | ~r1_tarski(X6,X7)) )),
% 1.88/0.63    inference(superposition,[],[f42,f50])).
% 1.88/0.63  fof(f50,plain,(
% 1.88/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.88/0.63    inference(cnf_transformation,[],[f28])).
% 1.88/0.63  fof(f28,plain,(
% 1.88/0.63    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.88/0.63    inference(ennf_transformation,[],[f5])).
% 1.88/0.63  fof(f5,axiom,(
% 1.88/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.88/0.63  fof(f42,plain,(
% 1.88/0.63    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.88/0.63    inference(cnf_transformation,[],[f4])).
% 1.88/0.63  fof(f4,axiom,(
% 1.88/0.63    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.88/0.63  fof(f208,plain,(
% 1.88/0.63    ~r1_tarski(k1_tarski(sK0),k1_tarski(sK0))),
% 1.88/0.63    inference(subsumption_resolution,[],[f205,f38])).
% 1.88/0.63  fof(f38,plain,(
% 1.88/0.63    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.88/0.63    inference(cnf_transformation,[],[f7])).
% 1.88/0.63  fof(f7,axiom,(
% 1.88/0.63    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.88/0.63  fof(f205,plain,(
% 1.88/0.63    ~r1_tarski(k1_tarski(sK0),k1_tarski(sK0)) | ~r1_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 1.88/0.63    inference(trivial_inequality_removal,[],[f204])).
% 1.88/0.63  fof(f204,plain,(
% 1.88/0.63    k1_tarski(sK0) != k1_tarski(sK0) | ~r1_tarski(k1_tarski(sK0),k1_tarski(sK0)) | ~r1_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 1.88/0.63    inference(superposition,[],[f202,f51])).
% 1.88/0.63  fof(f51,plain,(
% 1.88/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.88/0.63    inference(cnf_transformation,[],[f29])).
% 1.88/0.63  fof(f29,plain,(
% 1.88/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.88/0.63    inference(ennf_transformation,[],[f24])).
% 1.88/0.63  fof(f24,plain,(
% 1.88/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 1.88/0.63    inference(unused_predicate_definition_removal,[],[f9])).
% 1.88/0.63  fof(f9,axiom,(
% 1.88/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.88/0.63  fof(f202,plain,(
% 1.88/0.63    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_xboole_0) | ~r1_tarski(k1_tarski(sK0),k1_tarski(sK0))),
% 1.88/0.63    inference(superposition,[],[f190,f129])).
% 1.88/0.63  fof(f129,plain,(
% 1.88/0.63    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k4_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X0,X1)) )),
% 1.88/0.63    inference(backward_demodulation,[],[f85,f126])).
% 1.88/0.63  fof(f126,plain,(
% 1.88/0.63    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X3,k1_xboole_0)) )),
% 1.88/0.63    inference(superposition,[],[f47,f107])).
% 1.88/0.63  fof(f107,plain,(
% 1.88/0.63    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(X3,k1_xboole_0)) )),
% 1.88/0.63    inference(resolution,[],[f101,f66])).
% 1.88/0.63  fof(f66,plain,(
% 1.88/0.63    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 1.88/0.63    inference(superposition,[],[f42,f43])).
% 1.88/0.63  fof(f43,plain,(
% 1.88/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.88/0.63    inference(cnf_transformation,[],[f1])).
% 1.88/0.63  fof(f1,axiom,(
% 1.88/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.88/0.63  fof(f101,plain,(
% 1.88/0.63    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.88/0.63    inference(resolution,[],[f82,f38])).
% 1.88/0.63  fof(f82,plain,(
% 1.88/0.63    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | ~r1_tarski(X2,X3) | k1_xboole_0 = X2) )),
% 1.88/0.63    inference(superposition,[],[f57,f51])).
% 1.88/0.63  fof(f57,plain,(
% 1.88/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.88/0.63    inference(cnf_transformation,[],[f36])).
% 1.88/0.63  fof(f36,plain,(
% 1.88/0.63    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.88/0.63    inference(nnf_transformation,[],[f2])).
% 1.88/0.63  fof(f2,axiom,(
% 1.88/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.88/0.63  fof(f47,plain,(
% 1.88/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.88/0.63    inference(cnf_transformation,[],[f3])).
% 1.88/0.63  fof(f3,axiom,(
% 1.88/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.88/0.63  fof(f85,plain,(
% 1.88/0.63    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k5_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X0,X1)) )),
% 1.88/0.63    inference(superposition,[],[f46,f57])).
% 1.88/0.63  fof(f46,plain,(
% 1.88/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.88/0.63    inference(cnf_transformation,[],[f10])).
% 1.88/0.63  fof(f10,axiom,(
% 1.88/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.88/0.63  fof(f190,plain,(
% 1.88/0.63    k1_tarski(sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 1.88/0.63    inference(forward_demodulation,[],[f186,f40])).
% 1.88/0.63  fof(f186,plain,(
% 1.88/0.63    k2_tarski(sK0,sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 1.88/0.63    inference(backward_demodulation,[],[f72,f184])).
% 1.88/0.63  fof(f184,plain,(
% 1.88/0.63    sK0 = sK1),
% 1.88/0.63    inference(subsumption_resolution,[],[f183,f65])).
% 1.88/0.63  fof(f65,plain,(
% 1.88/0.63    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.88/0.63    inference(equality_resolution,[],[f52])).
% 1.88/0.63  fof(f52,plain,(
% 1.88/0.63    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.88/0.63    inference(cnf_transformation,[],[f35])).
% 1.88/0.63  fof(f35,plain,(
% 1.88/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.88/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 1.88/0.63  fof(f34,plain,(
% 1.88/0.63    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.88/0.63    introduced(choice_axiom,[])).
% 1.88/0.63  fof(f33,plain,(
% 1.88/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.88/0.63    inference(rectify,[],[f32])).
% 1.88/0.63  fof(f32,plain,(
% 1.88/0.63    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.88/0.63    inference(nnf_transformation,[],[f11])).
% 1.88/0.63  fof(f11,axiom,(
% 1.88/0.63    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.88/0.63  fof(f183,plain,(
% 1.88/0.63    sK0 = sK1 | r2_hidden(sK1,k1_tarski(sK0))),
% 1.88/0.63    inference(resolution,[],[f161,f49])).
% 1.88/0.63  fof(f49,plain,(
% 1.88/0.63    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.88/0.63    inference(cnf_transformation,[],[f27])).
% 1.88/0.63  fof(f27,plain,(
% 1.88/0.63    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.88/0.63    inference(ennf_transformation,[],[f19])).
% 1.88/0.63  fof(f19,axiom,(
% 1.88/0.63    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.88/0.63  fof(f161,plain,(
% 1.88/0.63    ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | sK0 = sK1),
% 1.88/0.63    inference(trivial_inequality_removal,[],[f160])).
% 1.88/0.63  fof(f160,plain,(
% 1.88/0.63    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | sK0 = sK1),
% 1.88/0.63    inference(superposition,[],[f159,f48])).
% 1.88/0.63  fof(f48,plain,(
% 1.88/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.88/0.63    inference(cnf_transformation,[],[f26])).
% 1.88/0.63  fof(f26,plain,(
% 1.88/0.63    ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 1.88/0.63    inference(ennf_transformation,[],[f21])).
% 1.88/0.63  fof(f21,axiom,(
% 1.88/0.63    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 1.88/0.63  fof(f159,plain,(
% 1.88/0.63    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 1.88/0.63    inference(superposition,[],[f72,f86])).
% 1.88/0.63  fof(f86,plain,(
% 1.88/0.63    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = k5_xboole_0(X3,X2) | ~r1_xboole_0(X2,X3)) )),
% 1.88/0.63    inference(superposition,[],[f46,f51])).
% 1.88/0.63  fof(f72,plain,(
% 1.88/0.63    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.88/0.63    inference(superposition,[],[f37,f44])).
% 1.88/0.63  fof(f37,plain,(
% 1.88/0.63    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.88/0.63    inference(cnf_transformation,[],[f31])).
% 1.88/0.63  fof(f31,plain,(
% 1.88/0.63    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.88/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f30])).
% 1.88/0.63  fof(f30,plain,(
% 1.88/0.63    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.88/0.63    introduced(choice_axiom,[])).
% 1.88/0.63  fof(f25,plain,(
% 1.88/0.63    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.88/0.63    inference(ennf_transformation,[],[f23])).
% 1.88/0.63  fof(f23,negated_conjecture,(
% 1.88/0.63    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.88/0.63    inference(negated_conjecture,[],[f22])).
% 1.88/0.63  fof(f22,conjecture,(
% 1.88/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.88/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).
% 1.88/0.63  % SZS output end Proof for theBenchmark
% 1.88/0.63  % (13155)------------------------------
% 1.88/0.63  % (13155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.63  % (13155)Termination reason: Refutation
% 1.88/0.63  
% 1.88/0.63  % (13155)Memory used [KB]: 1791
% 1.88/0.63  % (13155)Time elapsed: 0.198 s
% 1.88/0.63  % (13155)------------------------------
% 1.88/0.63  % (13155)------------------------------
% 1.88/0.63  % (13145)Success in time 0.268 s
%------------------------------------------------------------------------------
