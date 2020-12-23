%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:11 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 208 expanded)
%              Number of leaves         :   14 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :  118 ( 412 expanded)
%              Number of equality atoms :   59 ( 218 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f617,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f616])).

fof(f616,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f608,f179])).

fof(f179,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f167,f40])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f167,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f123,f74])).

fof(f74,plain,(
    ! [X6,X5] : k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6))) ),
    inference(superposition,[],[f38,f66])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f65,f48])).

fof(f48,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(resolution,[],[f58,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f42,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f123,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(backward_demodulation,[],[f71,f116])).

fof(f116,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(forward_demodulation,[],[f106,f40])).

fof(f106,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f71,f66])).

fof(f71,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f38,f66])).

fof(f608,plain,(
    sK1 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) ),
    inference(backward_demodulation,[],[f53,f591])).

fof(f591,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK2) = k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)) ),
    inference(forward_demodulation,[],[f582,f40])).

fof(f582,plain,(
    k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k1_xboole_0) ),
    inference(superposition,[],[f123,f530])).

fof(f530,plain,(
    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))) ),
    inference(resolution,[],[f431,f29])).

fof(f29,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
    & r2_hidden(sK2,sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f431,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | k1_xboole_0 = k5_xboole_0(k3_enumset1(X1,X1,X1,X1,sK2),k3_xboole_0(sK1,k3_enumset1(X1,X1,X1,X1,sK2))) ) ),
    inference(forward_demodulation,[],[f422,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f422,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | k1_xboole_0 = k5_xboole_0(k3_enumset1(X1,X1,X1,X1,sK2),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,sK2),sK1)) ) ),
    inference(resolution,[],[f102,f30])).

fof(f30,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | k1_xboole_0 = k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X0),k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X0),X1)) ) ),
    inference(resolution,[],[f55,f58])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f36,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
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
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f53,plain,(
    sK1 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))) ),
    inference(definition_unfolding,[],[f31,f50,f52])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f32,f39])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f31,plain,(
    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (1877)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.50  % (1897)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (1880)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (1885)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (1885)Refutation not found, incomplete strategy% (1885)------------------------------
% 0.21/0.51  % (1885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1885)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1885)Memory used [KB]: 10746
% 0.21/0.51  % (1885)Time elapsed: 0.104 s
% 0.21/0.51  % (1885)------------------------------
% 0.21/0.51  % (1885)------------------------------
% 0.21/0.51  % (1882)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (1887)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (1904)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (1899)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (1887)Refutation not found, incomplete strategy% (1887)------------------------------
% 0.21/0.52  % (1887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1887)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.52  % (1889)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.26/0.52  
% 1.26/0.52  % (1887)Memory used [KB]: 10746
% 1.26/0.52  % (1887)Time elapsed: 0.114 s
% 1.26/0.52  % (1887)------------------------------
% 1.26/0.52  % (1887)------------------------------
% 1.26/0.52  % (1876)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.26/0.52  % (1896)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.26/0.52  % (1895)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.26/0.53  % (1881)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.26/0.53  % (1875)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.26/0.53  % (1873)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.26/0.53  % (1899)Refutation not found, incomplete strategy% (1899)------------------------------
% 1.26/0.53  % (1899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (1899)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (1899)Memory used [KB]: 10618
% 1.26/0.53  % (1899)Time elapsed: 0.095 s
% 1.26/0.53  % (1899)------------------------------
% 1.26/0.53  % (1899)------------------------------
% 1.26/0.53  % (1873)Refutation not found, incomplete strategy% (1873)------------------------------
% 1.26/0.53  % (1873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (1873)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (1873)Memory used [KB]: 1663
% 1.26/0.53  % (1873)Time elapsed: 0.125 s
% 1.26/0.53  % (1873)------------------------------
% 1.26/0.53  % (1873)------------------------------
% 1.26/0.53  % (1883)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.26/0.53  % (1886)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.26/0.53  % (1891)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.26/0.53  % (1891)Refutation not found, incomplete strategy% (1891)------------------------------
% 1.26/0.53  % (1891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (1891)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (1891)Memory used [KB]: 10618
% 1.26/0.53  % (1891)Time elapsed: 0.128 s
% 1.26/0.53  % (1891)------------------------------
% 1.26/0.53  % (1891)------------------------------
% 1.26/0.53  % (1879)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.44/0.54  % (1901)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.44/0.54  % (1904)Refutation not found, incomplete strategy% (1904)------------------------------
% 1.44/0.54  % (1904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (1904)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (1904)Memory used [KB]: 1663
% 1.44/0.54  % (1904)Time elapsed: 0.143 s
% 1.44/0.54  % (1904)------------------------------
% 1.44/0.54  % (1904)------------------------------
% 1.44/0.54  % (1903)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.44/0.54  % (1901)Refutation not found, incomplete strategy% (1901)------------------------------
% 1.44/0.54  % (1901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (1901)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (1901)Memory used [KB]: 6268
% 1.44/0.54  % (1901)Time elapsed: 0.142 s
% 1.44/0.54  % (1901)------------------------------
% 1.44/0.54  % (1901)------------------------------
% 1.44/0.54  % (1892)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.44/0.54  % (1903)Refutation not found, incomplete strategy% (1903)------------------------------
% 1.44/0.54  % (1903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (1903)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (1903)Memory used [KB]: 10746
% 1.44/0.54  % (1903)Time elapsed: 0.143 s
% 1.44/0.54  % (1903)------------------------------
% 1.44/0.54  % (1903)------------------------------
% 1.44/0.54  % (1894)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.44/0.54  % (1889)Refutation not found, incomplete strategy% (1889)------------------------------
% 1.44/0.54  % (1889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (1889)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (1889)Memory used [KB]: 1663
% 1.44/0.54  % (1889)Time elapsed: 0.104 s
% 1.44/0.54  % (1889)------------------------------
% 1.44/0.54  % (1889)------------------------------
% 1.44/0.54  % (1893)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.44/0.54  % (1898)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.44/0.54  % (1872)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.44/0.54  % (1902)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.44/0.55  % (1902)Refutation not found, incomplete strategy% (1902)------------------------------
% 1.44/0.55  % (1902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (1902)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (1902)Memory used [KB]: 6140
% 1.44/0.55  % (1902)Time elapsed: 0.140 s
% 1.44/0.55  % (1902)------------------------------
% 1.44/0.55  % (1902)------------------------------
% 1.44/0.55  % (1888)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.44/0.56  % (1900)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.44/0.56  % (1890)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.44/0.56  % (1900)Refutation not found, incomplete strategy% (1900)------------------------------
% 1.44/0.56  % (1900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (1900)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (1900)Memory used [KB]: 6268
% 1.44/0.56  % (1900)Time elapsed: 0.163 s
% 1.44/0.56  % (1900)------------------------------
% 1.44/0.56  % (1900)------------------------------
% 1.44/0.56  % (1893)Refutation not found, incomplete strategy% (1893)------------------------------
% 1.44/0.56  % (1893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (1893)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (1893)Memory used [KB]: 1663
% 1.44/0.56  % (1893)Time elapsed: 0.162 s
% 1.44/0.56  % (1893)------------------------------
% 1.44/0.56  % (1893)------------------------------
% 1.44/0.58  % (1879)Refutation found. Thanks to Tanya!
% 1.44/0.58  % SZS status Theorem for theBenchmark
% 1.44/0.58  % SZS output start Proof for theBenchmark
% 1.44/0.58  fof(f617,plain,(
% 1.44/0.58    $false),
% 1.44/0.58    inference(trivial_inequality_removal,[],[f616])).
% 1.44/0.58  fof(f616,plain,(
% 1.44/0.58    sK1 != sK1),
% 1.44/0.58    inference(superposition,[],[f608,f179])).
% 1.44/0.58  fof(f179,plain,(
% 1.44/0.58    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 1.44/0.58    inference(forward_demodulation,[],[f167,f40])).
% 1.44/0.58  fof(f40,plain,(
% 1.44/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.44/0.58    inference(cnf_transformation,[],[f6])).
% 1.44/0.58  fof(f6,axiom,(
% 1.44/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.44/0.58  fof(f167,plain,(
% 1.44/0.58    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 1.44/0.58    inference(superposition,[],[f123,f74])).
% 1.44/0.58  fof(f74,plain,(
% 1.44/0.58    ( ! [X6,X5] : (k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6)))) )),
% 1.44/0.58    inference(superposition,[],[f38,f66])).
% 1.44/0.58  fof(f66,plain,(
% 1.44/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.44/0.58    inference(forward_demodulation,[],[f65,f48])).
% 1.44/0.58  fof(f48,plain,(
% 1.44/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.44/0.58    inference(cnf_transformation,[],[f19])).
% 1.44/0.58  fof(f19,plain,(
% 1.44/0.58    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.44/0.58    inference(rectify,[],[f2])).
% 1.44/0.58  fof(f2,axiom,(
% 1.44/0.58    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.44/0.58  fof(f65,plain,(
% 1.44/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.44/0.58    inference(resolution,[],[f58,f60])).
% 1.44/0.58  fof(f60,plain,(
% 1.44/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.44/0.58    inference(equality_resolution,[],[f44])).
% 1.44/0.58  fof(f44,plain,(
% 1.44/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.44/0.58    inference(cnf_transformation,[],[f28])).
% 1.44/0.58  fof(f28,plain,(
% 1.44/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.58    inference(flattening,[],[f27])).
% 1.44/0.58  fof(f27,plain,(
% 1.44/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.58    inference(nnf_transformation,[],[f3])).
% 1.44/0.58  fof(f3,axiom,(
% 1.44/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.44/0.58  fof(f58,plain,(
% 1.44/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.44/0.58    inference(definition_unfolding,[],[f42,f39])).
% 1.44/0.58  fof(f39,plain,(
% 1.44/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.44/0.58    inference(cnf_transformation,[],[f5])).
% 1.44/0.58  fof(f5,axiom,(
% 1.44/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.44/0.58  fof(f42,plain,(
% 1.44/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f26])).
% 1.44/0.58  fof(f26,plain,(
% 1.44/0.58    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.44/0.58    inference(nnf_transformation,[],[f4])).
% 1.44/0.58  fof(f4,axiom,(
% 1.44/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.44/0.58  fof(f38,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.44/0.58    inference(cnf_transformation,[],[f7])).
% 1.44/0.58  fof(f7,axiom,(
% 1.44/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.44/0.58  fof(f123,plain,(
% 1.44/0.58    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 1.44/0.58    inference(backward_demodulation,[],[f71,f116])).
% 1.44/0.58  fof(f116,plain,(
% 1.44/0.58    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.44/0.58    inference(forward_demodulation,[],[f106,f40])).
% 1.44/0.58  fof(f106,plain,(
% 1.44/0.58    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X1,k1_xboole_0)) )),
% 1.44/0.58    inference(superposition,[],[f71,f66])).
% 1.44/0.58  fof(f71,plain,(
% 1.44/0.58    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 1.44/0.58    inference(superposition,[],[f38,f66])).
% 1.44/0.58  fof(f608,plain,(
% 1.44/0.58    sK1 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),
% 1.44/0.58    inference(backward_demodulation,[],[f53,f591])).
% 1.44/0.58  fof(f591,plain,(
% 1.44/0.58    k3_enumset1(sK0,sK0,sK0,sK0,sK2) = k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))),
% 1.44/0.58    inference(forward_demodulation,[],[f582,f40])).
% 1.44/0.58  fof(f582,plain,(
% 1.44/0.58    k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k1_xboole_0)),
% 1.44/0.58    inference(superposition,[],[f123,f530])).
% 1.44/0.58  fof(f530,plain,(
% 1.44/0.58    k1_xboole_0 = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2)))),
% 1.44/0.58    inference(resolution,[],[f431,f29])).
% 1.44/0.58  fof(f29,plain,(
% 1.44/0.58    r2_hidden(sK0,sK1)),
% 1.44/0.58    inference(cnf_transformation,[],[f23])).
% 1.44/0.58  fof(f23,plain,(
% 1.44/0.58    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1)),
% 1.44/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).
% 1.44/0.58  fof(f22,plain,(
% 1.44/0.58    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1))),
% 1.44/0.58    introduced(choice_axiom,[])).
% 1.44/0.58  fof(f21,plain,(
% 1.44/0.58    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 1.44/0.58    inference(flattening,[],[f20])).
% 1.44/0.58  fof(f20,plain,(
% 1.44/0.58    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 1.44/0.58    inference(ennf_transformation,[],[f18])).
% 1.44/0.58  fof(f18,negated_conjecture,(
% 1.44/0.58    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 1.44/0.58    inference(negated_conjecture,[],[f17])).
% 1.44/0.58  fof(f17,conjecture,(
% 1.44/0.58    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 1.44/0.58  fof(f431,plain,(
% 1.44/0.58    ( ! [X1] : (~r2_hidden(X1,sK1) | k1_xboole_0 = k5_xboole_0(k3_enumset1(X1,X1,X1,X1,sK2),k3_xboole_0(sK1,k3_enumset1(X1,X1,X1,X1,sK2)))) )),
% 1.44/0.58    inference(forward_demodulation,[],[f422,f47])).
% 1.44/0.58  fof(f47,plain,(
% 1.44/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f1])).
% 1.44/0.58  fof(f1,axiom,(
% 1.44/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.44/0.58  fof(f422,plain,(
% 1.44/0.58    ( ! [X1] : (~r2_hidden(X1,sK1) | k1_xboole_0 = k5_xboole_0(k3_enumset1(X1,X1,X1,X1,sK2),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,sK2),sK1))) )),
% 1.44/0.58    inference(resolution,[],[f102,f30])).
% 1.44/0.58  fof(f30,plain,(
% 1.44/0.58    r2_hidden(sK2,sK1)),
% 1.44/0.58    inference(cnf_transformation,[],[f23])).
% 1.44/0.58  fof(f102,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X2,X1) | k1_xboole_0 = k5_xboole_0(k3_enumset1(X2,X2,X2,X2,X0),k3_xboole_0(k3_enumset1(X2,X2,X2,X2,X0),X1))) )),
% 1.44/0.58    inference(resolution,[],[f55,f58])).
% 1.44/0.58  fof(f55,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.44/0.58    inference(definition_unfolding,[],[f36,f52])).
% 1.44/0.58  fof(f52,plain,(
% 1.44/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.44/0.58    inference(definition_unfolding,[],[f37,f51])).
% 1.44/0.58  fof(f51,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.44/0.58    inference(definition_unfolding,[],[f46,f49])).
% 1.44/0.58  fof(f49,plain,(
% 1.44/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f11])).
% 1.44/0.58  fof(f11,axiom,(
% 1.44/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.44/0.58  fof(f46,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f10])).
% 1.44/0.58  fof(f10,axiom,(
% 1.44/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.44/0.58  fof(f37,plain,(
% 1.44/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f9])).
% 1.44/0.58  fof(f9,axiom,(
% 1.44/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.44/0.58  fof(f36,plain,(
% 1.44/0.58    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.44/0.58    inference(cnf_transformation,[],[f25])).
% 1.44/0.58  fof(f25,plain,(
% 1.44/0.58    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.44/0.58    inference(flattening,[],[f24])).
% 1.44/0.58  fof(f24,plain,(
% 1.44/0.58    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.44/0.58    inference(nnf_transformation,[],[f16])).
% 1.44/0.58  fof(f16,axiom,(
% 1.44/0.58    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.44/0.58  fof(f53,plain,(
% 1.44/0.58    sK1 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK2))))),
% 1.44/0.58    inference(definition_unfolding,[],[f31,f50,f52])).
% 1.44/0.58  fof(f50,plain,(
% 1.44/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.44/0.58    inference(definition_unfolding,[],[f32,f39])).
% 1.44/0.58  fof(f32,plain,(
% 1.44/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.44/0.58    inference(cnf_transformation,[],[f8])).
% 1.44/0.58  fof(f8,axiom,(
% 1.44/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.44/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.44/0.58  fof(f31,plain,(
% 1.44/0.58    sK1 != k2_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 1.44/0.58    inference(cnf_transformation,[],[f23])).
% 1.44/0.58  % SZS output end Proof for theBenchmark
% 1.44/0.58  % (1879)------------------------------
% 1.44/0.58  % (1879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.58  % (1879)Termination reason: Refutation
% 1.44/0.58  
% 1.44/0.58  % (1879)Memory used [KB]: 2430
% 1.44/0.58  % (1879)Time elapsed: 0.171 s
% 1.44/0.58  % (1879)------------------------------
% 1.44/0.58  % (1879)------------------------------
% 1.44/0.58  % (1871)Success in time 0.218 s
%------------------------------------------------------------------------------
