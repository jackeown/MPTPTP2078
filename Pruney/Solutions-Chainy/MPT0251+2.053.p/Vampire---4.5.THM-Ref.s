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
% DateTime   : Thu Dec  3 12:38:42 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 215 expanded)
%              Number of leaves         :   14 (  67 expanded)
%              Depth                    :   17
%              Number of atoms          :  111 ( 289 expanded)
%              Number of equality atoms :   64 ( 208 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f463,plain,(
    $false ),
    inference(subsumption_resolution,[],[f462,f173])).

fof(f173,plain,(
    sK1 != k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f27,f114])).

fof(f114,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f51,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f51,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f33,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f27,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f462,plain,(
    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f458,f171])).

fof(f171,plain,(
    ! [X7] : k2_xboole_0(k1_xboole_0,X7) = X7 ),
    inference(superposition,[],[f114,f28])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

% (29954)Refutation not found, incomplete strategy% (29954)------------------------------
% (29954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29954)Termination reason: Refutation not found, incomplete strategy

% (29954)Memory used [KB]: 1663
% (29954)Time elapsed: 0.150 s
% (29954)------------------------------
% (29954)------------------------------
fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f458,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[],[f143,f418])).

fof(f418,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(backward_demodulation,[],[f159,f405])).

fof(f405,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f65,f404])).

fof(f404,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(X6,X6) ),
    inference(forward_demodulation,[],[f403,f256])).

fof(f256,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(forward_demodulation,[],[f237,f171])).

fof(f237,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f143,f28])).

fof(f403,plain,(
    ! [X6] : k4_xboole_0(X6,X6) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f379,f171])).

fof(f379,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X6),X6) ),
    inference(superposition,[],[f210,f28])).

fof(f210,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2)) = k4_xboole_0(X2,X2) ),
    inference(backward_demodulation,[],[f120,f203])).

fof(f203,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X1) = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f91,f114])).

fof(f91,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X0) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f90,f65])).

fof(f90,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f34,f54])).

fof(f54,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(resolution,[],[f38,f30])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f120,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f35,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f66,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f36,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f65,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f34,f53])).

fof(f53,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f38,f47])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f159,plain,(
    k4_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f34,f103])).

fof(f103,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f80,f38])).

fof(f80,plain,(
    r1_tarski(k1_tarski(sK0),sK1) ),
    inference(forward_demodulation,[],[f79,f29])).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f79,plain,(
    r1_tarski(k2_tarski(sK0,sK0),sK1) ),
    inference(resolution,[],[f77,f26])).

fof(f26,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_tarski(k2_tarski(X0,sK0),sK1) ) ),
    inference(resolution,[],[f45,f26])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f143,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(forward_demodulation,[],[f142,f125])).

fof(f125,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X2,X1),k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f124,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f124,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(k4_xboole_0(X2,X1),k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f117,f114])).

fof(f117,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X2,X1),X1) = k2_xboole_0(k4_xboole_0(X2,X1),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f67,f37])).

fof(f142,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X1,X0),X0) = k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f137,f37])).

fof(f137,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f37,f69])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f35,f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (29951)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (29940)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.19/0.51  % (29938)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.19/0.51  % (29959)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.19/0.51  % (29943)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.19/0.52  % (29956)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.19/0.52  % (29952)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.19/0.52  % (29936)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.19/0.53  % (29946)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.34/0.53  % (29958)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.34/0.53  % (29948)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.34/0.53  % (29939)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.34/0.53  % (29950)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.34/0.53  % (29960)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.34/0.54  % (29945)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.34/0.54  % (29941)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.34/0.54  % (29950)Refutation not found, incomplete strategy% (29950)------------------------------
% 1.34/0.54  % (29950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (29960)Refutation not found, incomplete strategy% (29960)------------------------------
% 1.34/0.54  % (29960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (29960)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (29960)Memory used [KB]: 10618
% 1.34/0.54  % (29960)Time elapsed: 0.126 s
% 1.34/0.54  % (29960)------------------------------
% 1.34/0.54  % (29960)------------------------------
% 1.34/0.54  % (29950)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (29950)Memory used [KB]: 1663
% 1.34/0.54  % (29950)Time elapsed: 0.090 s
% 1.34/0.54  % (29950)------------------------------
% 1.34/0.54  % (29950)------------------------------
% 1.34/0.54  % (29965)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.54  % (29949)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.34/0.54  % (29957)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.34/0.54  % (29952)Refutation not found, incomplete strategy% (29952)------------------------------
% 1.34/0.54  % (29952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (29952)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (29952)Memory used [KB]: 10618
% 1.34/0.54  % (29952)Time elapsed: 0.124 s
% 1.34/0.54  % (29952)------------------------------
% 1.34/0.54  % (29952)------------------------------
% 1.34/0.54  % (29948)Refutation not found, incomplete strategy% (29948)------------------------------
% 1.34/0.54  % (29948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (29948)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (29948)Memory used [KB]: 10618
% 1.34/0.54  % (29948)Time elapsed: 0.134 s
% 1.34/0.54  % (29948)------------------------------
% 1.34/0.54  % (29948)------------------------------
% 1.34/0.54  % (29961)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.34/0.54  % (29963)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.34/0.54  % (29964)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.34/0.54  % (29953)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.34/0.54  % (29963)Refutation not found, incomplete strategy% (29963)------------------------------
% 1.34/0.54  % (29963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (29963)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (29963)Memory used [KB]: 6140
% 1.34/0.54  % (29963)Time elapsed: 0.109 s
% 1.34/0.54  % (29963)------------------------------
% 1.34/0.54  % (29963)------------------------------
% 1.34/0.54  % (29943)Refutation found. Thanks to Tanya!
% 1.34/0.54  % SZS status Theorem for theBenchmark
% 1.34/0.54  % (29944)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.34/0.54  % (29942)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.54  % (29953)Refutation not found, incomplete strategy% (29953)------------------------------
% 1.34/0.54  % (29953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (29953)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (29953)Memory used [KB]: 1791
% 1.34/0.54  % (29953)Time elapsed: 0.139 s
% 1.34/0.54  % (29953)------------------------------
% 1.34/0.54  % (29953)------------------------------
% 1.34/0.55  % (29964)Refutation not found, incomplete strategy% (29964)------------------------------
% 1.34/0.55  % (29964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (29964)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (29964)Memory used [KB]: 10618
% 1.34/0.55  % (29964)Time elapsed: 0.139 s
% 1.34/0.55  % (29964)------------------------------
% 1.34/0.55  % (29964)------------------------------
% 1.34/0.55  % (29962)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.34/0.55  % (29947)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.34/0.55  % (29962)Refutation not found, incomplete strategy% (29962)------------------------------
% 1.34/0.55  % (29962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (29962)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (29962)Memory used [KB]: 6268
% 1.34/0.55  % (29962)Time elapsed: 0.139 s
% 1.34/0.55  % (29962)------------------------------
% 1.34/0.55  % (29962)------------------------------
% 1.34/0.55  % (29947)Refutation not found, incomplete strategy% (29947)------------------------------
% 1.34/0.55  % (29947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (29947)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (29947)Memory used [KB]: 6268
% 1.34/0.55  % (29947)Time elapsed: 0.140 s
% 1.34/0.55  % (29947)------------------------------
% 1.34/0.55  % (29947)------------------------------
% 1.34/0.55  % (29965)Refutation not found, incomplete strategy% (29965)------------------------------
% 1.34/0.55  % (29965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (29965)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (29965)Memory used [KB]: 1663
% 1.34/0.55  % (29965)Time elapsed: 0.140 s
% 1.34/0.55  % (29965)------------------------------
% 1.34/0.55  % (29965)------------------------------
% 1.34/0.55  % (29954)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.34/0.55  % (29946)Refutation not found, incomplete strategy% (29946)------------------------------
% 1.34/0.55  % (29946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (29946)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (29946)Memory used [KB]: 10618
% 1.34/0.55  % (29946)Time elapsed: 0.151 s
% 1.34/0.55  % (29946)------------------------------
% 1.34/0.55  % (29946)------------------------------
% 1.34/0.55  % SZS output start Proof for theBenchmark
% 1.34/0.55  fof(f463,plain,(
% 1.34/0.55    $false),
% 1.34/0.55    inference(subsumption_resolution,[],[f462,f173])).
% 1.34/0.55  fof(f173,plain,(
% 1.34/0.55    sK1 != k2_xboole_0(sK1,k1_tarski(sK0))),
% 1.34/0.55    inference(superposition,[],[f27,f114])).
% 1.34/0.55  fof(f114,plain,(
% 1.34/0.55    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 1.34/0.55    inference(superposition,[],[f51,f33])).
% 1.34/0.55  fof(f33,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.34/0.55    inference(cnf_transformation,[],[f14])).
% 1.34/0.55  fof(f14,axiom,(
% 1.34/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.34/0.55  fof(f51,plain,(
% 1.34/0.55    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 1.34/0.55    inference(superposition,[],[f33,f31])).
% 1.34/0.55  fof(f31,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f9])).
% 1.34/0.55  fof(f9,axiom,(
% 1.34/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.34/0.55  fof(f27,plain,(
% 1.34/0.55    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.34/0.55    inference(cnf_transformation,[],[f21])).
% 1.34/0.55  fof(f21,plain,(
% 1.34/0.55    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 1.34/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).
% 1.34/0.55  fof(f20,plain,(
% 1.34/0.55    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f18,plain,(
% 1.34/0.55    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.34/0.55    inference(ennf_transformation,[],[f17])).
% 1.34/0.55  fof(f17,negated_conjecture,(
% 1.34/0.55    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.34/0.55    inference(negated_conjecture,[],[f16])).
% 1.34/0.55  fof(f16,conjecture,(
% 1.34/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.34/0.55  fof(f462,plain,(
% 1.34/0.55    sK1 = k2_xboole_0(sK1,k1_tarski(sK0))),
% 1.34/0.55    inference(forward_demodulation,[],[f458,f171])).
% 1.34/0.55  fof(f171,plain,(
% 1.34/0.55    ( ! [X7] : (k2_xboole_0(k1_xboole_0,X7) = X7) )),
% 1.34/0.55    inference(superposition,[],[f114,f28])).
% 1.34/0.55  fof(f28,plain,(
% 1.34/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.34/0.55    inference(cnf_transformation,[],[f3])).
% 1.34/0.55  % (29954)Refutation not found, incomplete strategy% (29954)------------------------------
% 1.34/0.55  % (29954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (29954)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (29954)Memory used [KB]: 1663
% 1.34/0.55  % (29954)Time elapsed: 0.150 s
% 1.34/0.55  % (29954)------------------------------
% 1.34/0.55  % (29954)------------------------------
% 1.34/0.55  fof(f3,axiom,(
% 1.34/0.55    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.34/0.55  fof(f458,plain,(
% 1.34/0.55    k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(k1_xboole_0,sK1)),
% 1.34/0.55    inference(superposition,[],[f143,f418])).
% 1.34/0.55  fof(f418,plain,(
% 1.34/0.55    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.34/0.55    inference(backward_demodulation,[],[f159,f405])).
% 1.34/0.55  fof(f405,plain,(
% 1.34/0.55    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.34/0.55    inference(backward_demodulation,[],[f65,f404])).
% 1.34/0.55  fof(f404,plain,(
% 1.34/0.55    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(X6,X6)) )),
% 1.34/0.55    inference(forward_demodulation,[],[f403,f256])).
% 1.34/0.55  fof(f256,plain,(
% 1.34/0.55    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6) )),
% 1.34/0.55    inference(forward_demodulation,[],[f237,f171])).
% 1.34/0.55  fof(f237,plain,(
% 1.34/0.55    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6)) )),
% 1.34/0.55    inference(superposition,[],[f143,f28])).
% 1.34/0.55  fof(f403,plain,(
% 1.34/0.55    ( ! [X6] : (k4_xboole_0(X6,X6) = k4_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.34/0.55    inference(forward_demodulation,[],[f379,f171])).
% 1.34/0.55  fof(f379,plain,(
% 1.34/0.55    ( ! [X6] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X6),X6)) )),
% 1.34/0.55    inference(superposition,[],[f210,f28])).
% 1.34/0.55  fof(f210,plain,(
% 1.34/0.55    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2)) = k4_xboole_0(X2,X2)) )),
% 1.34/0.55    inference(backward_demodulation,[],[f120,f203])).
% 1.34/0.55  fof(f203,plain,(
% 1.34/0.55    ( ! [X2,X1] : (k4_xboole_0(X1,X1) = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 1.34/0.55    inference(superposition,[],[f91,f114])).
% 1.34/0.55  fof(f91,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.34/0.55    inference(forward_demodulation,[],[f90,f65])).
% 1.34/0.55  fof(f90,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.34/0.55    inference(superposition,[],[f34,f54])).
% 1.34/0.55  fof(f54,plain,(
% 1.34/0.55    ( ! [X2,X1] : (k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1) )),
% 1.34/0.55    inference(resolution,[],[f38,f30])).
% 1.34/0.55  fof(f30,plain,(
% 1.34/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.34/0.55    inference(cnf_transformation,[],[f7])).
% 1.34/0.55  fof(f7,axiom,(
% 1.34/0.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.34/0.55  fof(f38,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.34/0.55    inference(cnf_transformation,[],[f19])).
% 1.34/0.55  fof(f19,plain,(
% 1.34/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.34/0.55    inference(ennf_transformation,[],[f4])).
% 1.34/0.55  fof(f4,axiom,(
% 1.34/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.34/0.55  fof(f34,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.34/0.55    inference(cnf_transformation,[],[f2])).
% 1.34/0.55  fof(f2,axiom,(
% 1.34/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.34/0.55  fof(f120,plain,(
% 1.34/0.55    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X2))) )),
% 1.34/0.55    inference(superposition,[],[f35,f67])).
% 1.34/0.55  fof(f67,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 1.34/0.55    inference(forward_demodulation,[],[f66,f36])).
% 1.34/0.55  fof(f36,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.34/0.55    inference(cnf_transformation,[],[f8])).
% 1.34/0.55  fof(f8,axiom,(
% 1.34/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.34/0.55  fof(f66,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 1.34/0.55    inference(superposition,[],[f36,f35])).
% 1.34/0.55  fof(f35,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f6])).
% 1.34/0.55  fof(f6,axiom,(
% 1.34/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.34/0.55  fof(f65,plain,(
% 1.34/0.55    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.34/0.55    inference(superposition,[],[f34,f53])).
% 1.34/0.55  fof(f53,plain,(
% 1.34/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.34/0.55    inference(resolution,[],[f38,f47])).
% 1.34/0.55  fof(f47,plain,(
% 1.34/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.34/0.55    inference(equality_resolution,[],[f40])).
% 1.34/0.55  fof(f40,plain,(
% 1.34/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.34/0.55    inference(cnf_transformation,[],[f23])).
% 1.34/0.55  fof(f23,plain,(
% 1.34/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.55    inference(flattening,[],[f22])).
% 1.34/0.55  fof(f22,plain,(
% 1.34/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.55    inference(nnf_transformation,[],[f1])).
% 1.34/0.55  fof(f1,axiom,(
% 1.34/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.34/0.55  fof(f159,plain,(
% 1.34/0.55    k4_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 1.34/0.55    inference(superposition,[],[f34,f103])).
% 1.34/0.55  fof(f103,plain,(
% 1.34/0.55    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)),
% 1.34/0.55    inference(resolution,[],[f80,f38])).
% 1.34/0.55  fof(f80,plain,(
% 1.34/0.55    r1_tarski(k1_tarski(sK0),sK1)),
% 1.34/0.55    inference(forward_demodulation,[],[f79,f29])).
% 1.34/0.55  fof(f29,plain,(
% 1.34/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f10])).
% 1.34/0.55  fof(f10,axiom,(
% 1.34/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.34/0.55  fof(f79,plain,(
% 1.34/0.55    r1_tarski(k2_tarski(sK0,sK0),sK1)),
% 1.34/0.55    inference(resolution,[],[f77,f26])).
% 1.34/0.55  fof(f26,plain,(
% 1.34/0.55    r2_hidden(sK0,sK1)),
% 1.34/0.55    inference(cnf_transformation,[],[f21])).
% 1.34/0.55  fof(f77,plain,(
% 1.34/0.55    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k2_tarski(X0,sK0),sK1)) )),
% 1.34/0.55    inference(resolution,[],[f45,f26])).
% 1.34/0.55  fof(f45,plain,(
% 1.34/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f25])).
% 1.34/0.55  fof(f25,plain,(
% 1.34/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.34/0.55    inference(flattening,[],[f24])).
% 1.34/0.55  fof(f24,plain,(
% 1.34/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.34/0.55    inference(nnf_transformation,[],[f15])).
% 1.34/0.55  fof(f15,axiom,(
% 1.34/0.55    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.34/0.55  fof(f143,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 1.34/0.55    inference(forward_demodulation,[],[f142,f125])).
% 1.34/0.55  fof(f125,plain,(
% 1.34/0.55    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X2,X1),k2_xboole_0(X1,X2))) )),
% 1.34/0.55    inference(forward_demodulation,[],[f124,f37])).
% 1.34/0.55  fof(f37,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f5])).
% 1.34/0.55  fof(f5,axiom,(
% 1.34/0.55    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.34/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.34/0.55  fof(f124,plain,(
% 1.34/0.55    ( ! [X2,X1] : (k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(k4_xboole_0(X2,X1),k2_xboole_0(X1,X2))) )),
% 1.34/0.55    inference(forward_demodulation,[],[f117,f114])).
% 1.34/0.55  fof(f117,plain,(
% 1.34/0.55    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X2,X1),X1) = k2_xboole_0(k4_xboole_0(X2,X1),k2_xboole_0(X1,X2))) )),
% 1.34/0.55    inference(superposition,[],[f67,f37])).
% 1.34/0.55  fof(f142,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,X0),X0) = k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1))) )),
% 1.34/0.55    inference(forward_demodulation,[],[f137,f37])).
% 1.34/0.55  fof(f137,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 1.34/0.55    inference(superposition,[],[f37,f69])).
% 1.34/0.55  fof(f69,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.34/0.55    inference(superposition,[],[f35,f37])).
% 1.34/0.55  % SZS output end Proof for theBenchmark
% 1.34/0.55  % (29943)------------------------------
% 1.34/0.55  % (29943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (29943)Termination reason: Refutation
% 1.34/0.55  
% 1.34/0.55  % (29943)Memory used [KB]: 2046
% 1.34/0.55  % (29943)Time elapsed: 0.137 s
% 1.34/0.55  % (29943)------------------------------
% 1.34/0.55  % (29943)------------------------------
% 1.34/0.56  % (29935)Success in time 0.192 s
%------------------------------------------------------------------------------
