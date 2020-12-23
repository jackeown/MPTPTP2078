%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:54 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   50 (  85 expanded)
%              Number of leaves         :   13 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :   86 ( 128 expanded)
%              Number of equality atoms :   28 (  55 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f349,plain,(
    $false ),
    inference(resolution,[],[f337,f79])).

fof(f79,plain,(
    ! [X0] : ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,X0),sK2) ),
    inference(resolution,[],[f48,f26])).

fof(f26,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f27,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f43])).

% (29585)Refutation not found, incomplete strategy% (29585)------------------------------
% (29585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29585)Termination reason: Refutation not found, incomplete strategy

% (29585)Memory used [KB]: 1663
% (29585)Time elapsed: 0.116 s
% (29585)------------------------------
% (29585)------------------------------
fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f337,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(superposition,[],[f152,f335])).

fof(f335,plain,(
    sK2 = k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) ),
    inference(resolution,[],[f157,f59])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) ),
    inference(superposition,[],[f49,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f33,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f34,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f157,plain,
    ( ~ r1_tarski(sK2,k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))))
    | sK2 = k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))) ),
    inference(resolution,[],[f142,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

% (29565)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f142,plain,(
    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),sK2) ),
    inference(forward_demodulation,[],[f105,f38])).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f105,plain,(
    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k3_enumset1(sK0,sK0,sK0,sK0,sK1))),sK2) ),
    inference(backward_demodulation,[],[f45,f64])).

fof(f64,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4)) ),
    inference(superposition,[],[f36,f38])).

fof(f36,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f45,plain,(
    r1_tarski(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),sK2) ),
    inference(definition_unfolding,[],[f25,f42,f44])).

fof(f25,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f152,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) ),
    inference(forward_demodulation,[],[f134,f38])).

fof(f134,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),X0))) ),
    inference(superposition,[],[f49,f64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : run_vampire %s %d
% 0.10/0.30  % Computer   : n009.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 20:23:56 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.15/0.42  % (29558)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.15/0.42  % (29559)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.15/0.44  % (29568)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.15/0.44  % (29575)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.15/0.45  % (29560)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.15/0.45  % (29555)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.15/0.45  % (29566)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.15/0.45  % (29566)Refutation not found, incomplete strategy% (29566)------------------------------
% 0.15/0.45  % (29566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.45  % (29566)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.45  
% 0.15/0.45  % (29566)Memory used [KB]: 6140
% 0.15/0.45  % (29566)Time elapsed: 0.104 s
% 0.15/0.45  % (29566)------------------------------
% 0.15/0.45  % (29566)------------------------------
% 0.15/0.45  % (29567)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.15/0.45  % (29567)Refutation not found, incomplete strategy% (29567)------------------------------
% 0.15/0.45  % (29567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.45  % (29567)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.45  
% 0.15/0.45  % (29567)Memory used [KB]: 10618
% 0.15/0.45  % (29567)Time elapsed: 0.103 s
% 0.15/0.45  % (29567)------------------------------
% 0.15/0.45  % (29567)------------------------------
% 0.15/0.45  % (29573)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.15/0.46  % (29582)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.15/0.46  % (29572)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.15/0.46  % (29580)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.15/0.46  % (29557)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.15/0.46  % (29572)Refutation not found, incomplete strategy% (29572)------------------------------
% 0.15/0.46  % (29572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.46  % (29572)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.46  
% 0.15/0.46  % (29572)Memory used [KB]: 1663
% 0.15/0.46  % (29572)Time elapsed: 0.111 s
% 0.15/0.46  % (29572)------------------------------
% 0.15/0.46  % (29572)------------------------------
% 0.15/0.46  % (29580)Refutation not found, incomplete strategy% (29580)------------------------------
% 0.15/0.46  % (29580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.46  % (29580)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.46  
% 0.15/0.46  % (29580)Memory used [KB]: 10618
% 0.15/0.46  % (29580)Time elapsed: 0.110 s
% 0.15/0.46  % (29580)------------------------------
% 0.15/0.46  % (29580)------------------------------
% 0.15/0.46  % (29573)Refutation not found, incomplete strategy% (29573)------------------------------
% 0.15/0.46  % (29573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.46  % (29556)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.15/0.46  % (29556)Refutation not found, incomplete strategy% (29556)------------------------------
% 0.15/0.46  % (29556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.46  % (29556)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.46  
% 0.15/0.46  % (29556)Memory used [KB]: 1663
% 0.15/0.46  % (29556)Time elapsed: 0.098 s
% 0.15/0.46  % (29556)------------------------------
% 0.15/0.46  % (29556)------------------------------
% 0.15/0.46  % (29573)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.46  
% 0.15/0.46  % (29573)Memory used [KB]: 1663
% 0.15/0.46  % (29573)Time elapsed: 0.101 s
% 0.15/0.46  % (29573)------------------------------
% 0.15/0.46  % (29573)------------------------------
% 0.15/0.47  % (29560)Refutation found. Thanks to Tanya!
% 0.15/0.47  % SZS status Theorem for theBenchmark
% 0.15/0.47  % (29582)Refutation not found, incomplete strategy% (29582)------------------------------
% 0.15/0.47  % (29582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.47  % (29585)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.15/0.47  % SZS output start Proof for theBenchmark
% 0.15/0.47  fof(f349,plain,(
% 0.15/0.47    $false),
% 0.15/0.47    inference(resolution,[],[f337,f79])).
% 0.15/0.47  fof(f79,plain,(
% 0.15/0.47    ( ! [X0] : (~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,X0),sK2)) )),
% 0.15/0.47    inference(resolution,[],[f48,f26])).
% 0.15/0.47  fof(f26,plain,(
% 0.15/0.47    ~r2_hidden(sK0,sK2)),
% 0.15/0.47    inference(cnf_transformation,[],[f20])).
% 0.15/0.47  fof(f20,plain,(
% 0.15/0.47    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 0.15/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).
% 0.15/0.47  fof(f19,plain,(
% 0.15/0.47    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 0.15/0.47    introduced(choice_axiom,[])).
% 0.15/0.47  fof(f18,plain,(
% 0.15/0.47    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 0.15/0.47    inference(ennf_transformation,[],[f17])).
% 0.15/0.47  fof(f17,negated_conjecture,(
% 0.15/0.47    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 0.15/0.47    inference(negated_conjecture,[],[f16])).
% 0.15/0.47  fof(f16,conjecture,(
% 0.15/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 0.15/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 0.15/0.47  fof(f48,plain,(
% 0.15/0.47    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)) )),
% 0.15/0.47    inference(definition_unfolding,[],[f27,f44])).
% 0.15/0.47  fof(f44,plain,(
% 0.15/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.15/0.47    inference(definition_unfolding,[],[f35,f43])).
% 0.15/0.47  % (29585)Refutation not found, incomplete strategy% (29585)------------------------------
% 0.15/0.47  % (29585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.47  % (29585)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.47  
% 0.15/0.47  % (29585)Memory used [KB]: 1663
% 0.15/0.47  % (29585)Time elapsed: 0.116 s
% 0.15/0.47  % (29585)------------------------------
% 0.15/0.47  % (29585)------------------------------
% 0.15/0.47  fof(f43,plain,(
% 0.15/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.15/0.47    inference(definition_unfolding,[],[f39,f41])).
% 0.15/0.47  fof(f41,plain,(
% 0.15/0.47    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.15/0.47    inference(cnf_transformation,[],[f10])).
% 0.15/0.47  fof(f10,axiom,(
% 0.15/0.47    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.15/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.15/0.47  fof(f39,plain,(
% 0.15/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.15/0.47    inference(cnf_transformation,[],[f9])).
% 0.15/0.47  fof(f9,axiom,(
% 0.15/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.15/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.15/0.47  fof(f35,plain,(
% 0.15/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.15/0.47    inference(cnf_transformation,[],[f8])).
% 0.15/0.47  fof(f8,axiom,(
% 0.15/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.15/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.15/0.47  fof(f27,plain,(
% 0.15/0.47    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.15/0.47    inference(cnf_transformation,[],[f22])).
% 0.15/0.47  fof(f22,plain,(
% 0.15/0.47    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.15/0.47    inference(flattening,[],[f21])).
% 0.15/0.47  fof(f21,plain,(
% 0.15/0.47    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.15/0.47    inference(nnf_transformation,[],[f15])).
% 0.15/0.47  fof(f15,axiom,(
% 0.15/0.47    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.15/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.15/0.47  fof(f337,plain,(
% 0.15/0.47    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)),
% 0.15/0.47    inference(superposition,[],[f152,f335])).
% 0.15/0.47  fof(f335,plain,(
% 0.15/0.47    sK2 = k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))))),
% 0.15/0.47    inference(resolution,[],[f157,f59])).
% 0.15/0.47  fof(f59,plain,(
% 0.15/0.47    ( ! [X0,X1] : (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))))) )),
% 0.15/0.47    inference(superposition,[],[f49,f40])).
% 0.15/0.47  fof(f40,plain,(
% 0.15/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.15/0.47    inference(cnf_transformation,[],[f1])).
% 0.15/0.47  fof(f1,axiom,(
% 0.15/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.15/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.15/0.47  fof(f49,plain,(
% 0.15/0.47    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 0.15/0.47    inference(definition_unfolding,[],[f33,f42])).
% 0.15/0.47  fof(f42,plain,(
% 0.15/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.15/0.47    inference(definition_unfolding,[],[f34,f37])).
% 0.15/0.47  fof(f37,plain,(
% 0.15/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.15/0.47    inference(cnf_transformation,[],[f4])).
% 0.15/0.47  fof(f4,axiom,(
% 0.15/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.15/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.15/0.47  fof(f34,plain,(
% 0.15/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.15/0.47    inference(cnf_transformation,[],[f7])).
% 0.15/0.47  fof(f7,axiom,(
% 0.15/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.15/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.15/0.47  fof(f33,plain,(
% 0.15/0.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.15/0.47    inference(cnf_transformation,[],[f5])).
% 0.15/0.47  fof(f5,axiom,(
% 0.15/0.47    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.15/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.15/0.47  fof(f157,plain,(
% 0.15/0.47    ~r1_tarski(sK2,k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))))) | sK2 = k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))))),
% 0.15/0.47    inference(resolution,[],[f142,f32])).
% 0.15/0.47  fof(f32,plain,(
% 0.15/0.47    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.15/0.47    inference(cnf_transformation,[],[f24])).
% 0.15/0.47  fof(f24,plain,(
% 0.15/0.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.15/0.47    inference(flattening,[],[f23])).
% 0.15/0.47  % (29565)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.15/0.47  fof(f23,plain,(
% 0.15/0.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.15/0.47    inference(nnf_transformation,[],[f3])).
% 0.15/0.47  fof(f3,axiom,(
% 0.15/0.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.15/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.15/0.47  fof(f142,plain,(
% 0.15/0.47    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),sK2)),
% 0.15/0.47    inference(forward_demodulation,[],[f105,f38])).
% 0.15/0.47  fof(f38,plain,(
% 0.15/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.15/0.47    inference(cnf_transformation,[],[f2])).
% 0.15/0.47  fof(f2,axiom,(
% 0.15/0.47    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.15/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.15/0.47  fof(f105,plain,(
% 0.15/0.47    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k3_enumset1(sK0,sK0,sK0,sK0,sK1))),sK2)),
% 0.15/0.47    inference(backward_demodulation,[],[f45,f64])).
% 0.15/0.47  fof(f64,plain,(
% 0.15/0.47    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))) )),
% 0.15/0.47    inference(superposition,[],[f36,f38])).
% 0.15/0.47  fof(f36,plain,(
% 0.15/0.47    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.15/0.47    inference(cnf_transformation,[],[f6])).
% 0.15/0.47  fof(f6,axiom,(
% 0.15/0.47    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.15/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.15/0.47  fof(f45,plain,(
% 0.15/0.47    r1_tarski(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),sK2)),
% 0.15/0.47    inference(definition_unfolding,[],[f25,f42,f44])).
% 0.15/0.47  fof(f25,plain,(
% 0.15/0.47    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 0.15/0.47    inference(cnf_transformation,[],[f20])).
% 0.15/0.47  fof(f152,plain,(
% 0.15/0.47    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))))) )),
% 0.15/0.47    inference(forward_demodulation,[],[f134,f38])).
% 0.15/0.47  fof(f134,plain,(
% 0.15/0.47    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),X0)))) )),
% 0.15/0.47    inference(superposition,[],[f49,f64])).
% 0.15/0.47  % SZS output end Proof for theBenchmark
% 0.15/0.47  % (29560)------------------------------
% 0.15/0.47  % (29560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.47  % (29560)Termination reason: Refutation
% 0.15/0.47  
% 0.15/0.47  % (29560)Memory used [KB]: 2046
% 0.15/0.47  % (29560)Time elapsed: 0.095 s
% 0.15/0.47  % (29560)------------------------------
% 0.15/0.47  % (29560)------------------------------
% 0.15/0.48  % (29554)Success in time 0.161 s
%------------------------------------------------------------------------------
