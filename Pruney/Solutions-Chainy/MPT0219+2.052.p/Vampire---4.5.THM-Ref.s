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
% DateTime   : Thu Dec  3 12:35:27 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 285 expanded)
%              Number of leaves         :   18 (  92 expanded)
%              Depth                    :   20
%              Number of atoms          :  212 ( 475 expanded)
%              Number of equality atoms :  109 ( 331 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f468,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f467])).

fof(f467,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f43,f409])).

fof(f409,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f406,f100])).

fof(f100,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f46,f75])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f68,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f406,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
      | sK0 = X0 ) ),
    inference(forward_demodulation,[],[f399,f207])).

fof(f207,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = X4 ),
    inference(forward_demodulation,[],[f204,f52])).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f204,plain,(
    ! [X4] : k5_xboole_0(X4,k1_xboole_0) = k4_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f76,f165])).

fof(f165,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(X5,k4_xboole_0(X5,k1_xboole_0)) ),
    inference(superposition,[],[f97,f150])).

fof(f150,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f143,f52])).

fof(f143,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f76,f116])).

fof(f116,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[],[f96,f72])).

fof(f72,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f69,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f97,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f70,f53,f53])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f51,f53])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f399,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0))
      | sK0 = X0 ) ),
    inference(superposition,[],[f125,f374])).

fof(f374,plain,(
    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f333,f52])).

fof(f333,plain,(
    k1_xboole_0 = k5_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f315,f217])).

fof(f217,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f142,f208])).

fof(f208,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(X5,X5) ),
    inference(backward_demodulation,[],[f165,f207])).

fof(f142,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f76,f98])).

fof(f98,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f71,f53])).

fof(f71,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f315,plain,(
    k1_xboole_0 = k5_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f232,f128])).

% (28683)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% (28687)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (28706)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (28702)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (28688)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (28706)Refutation not found, incomplete strategy% (28706)------------------------------
% (28706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28706)Termination reason: Refutation not found, incomplete strategy

% (28706)Memory used [KB]: 1663
% (28706)Time elapsed: 0.131 s
% (28706)------------------------------
% (28706)------------------------------
% (28700)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% (28697)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (28704)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% (28703)Refutation not found, incomplete strategy% (28703)------------------------------
% (28703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28703)Termination reason: Refutation not found, incomplete strategy

% (28703)Memory used [KB]: 6268
% (28703)Time elapsed: 0.140 s
% (28703)------------------------------
% (28703)------------------------------
% (28698)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f128,plain,(
    ! [X2] : k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)),X2)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X2) ),
    inference(superposition,[],[f50,f77])).

fof(f77,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f42,f75,f44,f75,f75])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f232,plain,(
    ! [X2,X1] : k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(superposition,[],[f217,f50])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))
      | X0 = X2 ) ),
    inference(resolution,[],[f110,f101])).

fof(f101,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f45,f75])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f110,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f63,f53])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f43,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:55:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (28690)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (28682)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (28678)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (28681)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.25/0.53  % (28680)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.25/0.53  % (28685)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.25/0.53  % (28689)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.25/0.53  % (28677)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.25/0.53  % (28684)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.25/0.53  % (28686)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.25/0.53  % (28679)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.25/0.53  % (28693)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.25/0.53  % (28693)Refutation not found, incomplete strategy% (28693)------------------------------
% 1.25/0.53  % (28693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (28693)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (28693)Memory used [KB]: 10618
% 1.25/0.53  % (28693)Time elapsed: 0.118 s
% 1.25/0.53  % (28693)------------------------------
% 1.25/0.53  % (28693)------------------------------
% 1.25/0.54  % (28699)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.25/0.54  % (28692)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.25/0.54  % (28705)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.25/0.54  % (28691)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.25/0.54  % (28694)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.25/0.54  % (28701)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.25/0.54  % (28695)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.25/0.54  % (28691)Refutation not found, incomplete strategy% (28691)------------------------------
% 1.25/0.54  % (28691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (28691)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (28691)Memory used [KB]: 1663
% 1.25/0.54  % (28691)Time elapsed: 0.100 s
% 1.25/0.54  % (28691)------------------------------
% 1.25/0.54  % (28691)------------------------------
% 1.25/0.54  % (28695)Refutation not found, incomplete strategy% (28695)------------------------------
% 1.25/0.54  % (28695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (28695)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (28695)Memory used [KB]: 1663
% 1.25/0.54  % (28695)Time elapsed: 0.127 s
% 1.25/0.54  % (28695)------------------------------
% 1.25/0.54  % (28695)------------------------------
% 1.25/0.54  % (28696)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.25/0.54  % (28703)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.25/0.54  % (28682)Refutation found. Thanks to Tanya!
% 1.25/0.54  % SZS status Theorem for theBenchmark
% 1.25/0.54  % SZS output start Proof for theBenchmark
% 1.25/0.54  fof(f468,plain,(
% 1.25/0.54    $false),
% 1.25/0.54    inference(trivial_inequality_removal,[],[f467])).
% 1.25/0.54  fof(f467,plain,(
% 1.25/0.54    sK0 != sK0),
% 1.25/0.54    inference(superposition,[],[f43,f409])).
% 1.25/0.54  fof(f409,plain,(
% 1.25/0.54    sK0 = sK1),
% 1.25/0.54    inference(resolution,[],[f406,f100])).
% 1.25/0.54  fof(f100,plain,(
% 1.25/0.54    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 1.25/0.54    inference(equality_resolution,[],[f99])).
% 1.25/0.54  fof(f99,plain,(
% 1.25/0.54    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 1.25/0.54    inference(equality_resolution,[],[f80])).
% 1.25/0.54  fof(f80,plain,(
% 1.25/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.25/0.54    inference(definition_unfolding,[],[f46,f75])).
% 1.25/0.54  fof(f75,plain,(
% 1.25/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.25/0.54    inference(definition_unfolding,[],[f49,f74])).
% 1.25/0.54  fof(f74,plain,(
% 1.25/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.25/0.54    inference(definition_unfolding,[],[f68,f73])).
% 1.25/0.54  fof(f73,plain,(
% 1.25/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f15])).
% 1.25/0.54  fof(f15,axiom,(
% 1.25/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.25/0.54  fof(f68,plain,(
% 1.25/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f14])).
% 1.25/0.54  fof(f14,axiom,(
% 1.25/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.25/0.54  fof(f49,plain,(
% 1.25/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f13])).
% 1.25/0.54  fof(f13,axiom,(
% 1.25/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.25/0.54  fof(f46,plain,(
% 1.25/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.25/0.54    inference(cnf_transformation,[],[f31])).
% 1.25/0.54  fof(f31,plain,(
% 1.25/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.25/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 1.25/0.54  fof(f30,plain,(
% 1.25/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f29,plain,(
% 1.25/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.25/0.54    inference(rectify,[],[f28])).
% 1.25/0.54  fof(f28,plain,(
% 1.25/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.25/0.54    inference(nnf_transformation,[],[f12])).
% 1.25/0.54  fof(f12,axiom,(
% 1.25/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.25/0.54  fof(f406,plain,(
% 1.25/0.54    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) | sK0 = X0) )),
% 1.25/0.54    inference(forward_demodulation,[],[f399,f207])).
% 1.25/0.54  fof(f207,plain,(
% 1.25/0.54    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = X4) )),
% 1.25/0.54    inference(forward_demodulation,[],[f204,f52])).
% 1.25/0.54  fof(f52,plain,(
% 1.25/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.25/0.54    inference(cnf_transformation,[],[f8])).
% 1.25/0.54  fof(f8,axiom,(
% 1.25/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.25/0.54  fof(f204,plain,(
% 1.25/0.54    ( ! [X4] : (k5_xboole_0(X4,k1_xboole_0) = k4_xboole_0(X4,k1_xboole_0)) )),
% 1.25/0.54    inference(superposition,[],[f76,f165])).
% 1.25/0.54  fof(f165,plain,(
% 1.25/0.54    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(X5,k4_xboole_0(X5,k1_xboole_0))) )),
% 1.25/0.54    inference(superposition,[],[f97,f150])).
% 1.25/0.54  fof(f150,plain,(
% 1.25/0.54    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 1.25/0.54    inference(forward_demodulation,[],[f143,f52])).
% 1.25/0.54  fof(f143,plain,(
% 1.25/0.54    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.25/0.54    inference(superposition,[],[f76,f116])).
% 1.25/0.54  fof(f116,plain,(
% 1.25/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.25/0.54    inference(resolution,[],[f96,f72])).
% 1.25/0.54  fof(f72,plain,(
% 1.25/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f6])).
% 1.25/0.54  fof(f6,axiom,(
% 1.25/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.25/0.54  fof(f96,plain,(
% 1.25/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.25/0.54    inference(definition_unfolding,[],[f69,f53])).
% 1.25/0.54  fof(f53,plain,(
% 1.25/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.25/0.54    inference(cnf_transformation,[],[f7])).
% 1.25/0.54  fof(f7,axiom,(
% 1.25/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.25/0.54  fof(f69,plain,(
% 1.25/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f25])).
% 1.25/0.54  fof(f25,plain,(
% 1.25/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.25/0.54    inference(ennf_transformation,[],[f5])).
% 1.25/0.54  fof(f5,axiom,(
% 1.25/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.25/0.54  fof(f97,plain,(
% 1.25/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.25/0.54    inference(definition_unfolding,[],[f70,f53,f53])).
% 1.25/0.54  fof(f70,plain,(
% 1.25/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f1])).
% 1.25/0.54  fof(f1,axiom,(
% 1.25/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.25/0.54  fof(f76,plain,(
% 1.25/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.25/0.54    inference(definition_unfolding,[],[f51,f53])).
% 1.25/0.54  fof(f51,plain,(
% 1.25/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.25/0.54    inference(cnf_transformation,[],[f4])).
% 1.25/0.54  fof(f4,axiom,(
% 1.25/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.25/0.54  fof(f399,plain,(
% 1.25/0.54    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0)) | sK0 = X0) )),
% 1.25/0.54    inference(superposition,[],[f125,f374])).
% 1.25/0.54  fof(f374,plain,(
% 1.25/0.54    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.25/0.54    inference(superposition,[],[f333,f52])).
% 1.25/0.54  fof(f333,plain,(
% 1.25/0.54    k1_xboole_0 = k5_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 1.25/0.54    inference(forward_demodulation,[],[f315,f217])).
% 1.25/0.54  fof(f217,plain,(
% 1.25/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.25/0.54    inference(backward_demodulation,[],[f142,f208])).
% 1.25/0.54  fof(f208,plain,(
% 1.25/0.54    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(X5,X5)) )),
% 1.25/0.54    inference(backward_demodulation,[],[f165,f207])).
% 1.25/0.54  fof(f142,plain,(
% 1.25/0.54    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.25/0.54    inference(superposition,[],[f76,f98])).
% 1.25/0.54  fof(f98,plain,(
% 1.25/0.54    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.25/0.54    inference(definition_unfolding,[],[f71,f53])).
% 1.25/0.54  fof(f71,plain,(
% 1.25/0.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.25/0.54    inference(cnf_transformation,[],[f22])).
% 1.25/0.54  fof(f22,plain,(
% 1.25/0.54    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.25/0.54    inference(rectify,[],[f3])).
% 1.25/0.54  fof(f3,axiom,(
% 1.25/0.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.25/0.54  fof(f315,plain,(
% 1.25/0.54    k1_xboole_0 = k5_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.25/0.54    inference(superposition,[],[f232,f128])).
% 1.25/0.54  % (28683)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.55  % (28687)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.25/0.55  % (28706)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.25/0.55  % (28702)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.25/0.55  % (28688)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.25/0.55  % (28706)Refutation not found, incomplete strategy% (28706)------------------------------
% 1.25/0.55  % (28706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.55  % (28706)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.55  
% 1.25/0.55  % (28706)Memory used [KB]: 1663
% 1.25/0.55  % (28706)Time elapsed: 0.131 s
% 1.25/0.55  % (28706)------------------------------
% 1.25/0.55  % (28706)------------------------------
% 1.25/0.55  % (28700)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.25/0.55  % (28697)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.25/0.55  % (28704)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.47/0.56  % (28703)Refutation not found, incomplete strategy% (28703)------------------------------
% 1.47/0.56  % (28703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (28703)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (28703)Memory used [KB]: 6268
% 1.47/0.56  % (28703)Time elapsed: 0.140 s
% 1.47/0.56  % (28703)------------------------------
% 1.47/0.56  % (28703)------------------------------
% 1.47/0.56  % (28698)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.47/0.56  fof(f128,plain,(
% 1.47/0.56    ( ! [X2] : (k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)),X2)) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X2)) )),
% 1.47/0.56    inference(superposition,[],[f50,f77])).
% 1.47/0.56  fof(f77,plain,(
% 1.47/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.47/0.56    inference(definition_unfolding,[],[f42,f75,f44,f75,f75])).
% 1.47/0.56  fof(f44,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f10])).
% 1.47/0.56  fof(f10,axiom,(
% 1.47/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.47/0.56  fof(f42,plain,(
% 1.47/0.56    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.47/0.56    inference(cnf_transformation,[],[f27])).
% 1.47/0.56  fof(f27,plain,(
% 1.47/0.56    sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26])).
% 1.47/0.56  fof(f26,plain,(
% 1.47/0.56    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f23,plain,(
% 1.47/0.56    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.47/0.56    inference(ennf_transformation,[],[f21])).
% 1.47/0.56  fof(f21,negated_conjecture,(
% 1.47/0.56    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.47/0.56    inference(negated_conjecture,[],[f20])).
% 1.47/0.56  fof(f20,conjecture,(
% 1.47/0.56    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 1.47/0.56  fof(f50,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f9])).
% 1.47/0.56  fof(f9,axiom,(
% 1.47/0.56    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.47/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.47/0.56  fof(f232,plain,(
% 1.47/0.56    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))) )),
% 1.47/0.56    inference(superposition,[],[f217,f50])).
% 1.47/0.56  fof(f125,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) | X0 = X2) )),
% 1.47/0.56    inference(resolution,[],[f110,f101])).
% 1.47/0.56  fof(f101,plain,(
% 1.47/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.47/0.56    inference(equality_resolution,[],[f81])).
% 1.47/0.56  fof(f81,plain,(
% 1.47/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.47/0.56    inference(definition_unfolding,[],[f45,f75])).
% 1.47/0.56  fof(f45,plain,(
% 1.47/0.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.47/0.56    inference(cnf_transformation,[],[f31])).
% 1.47/0.56  fof(f110,plain,(
% 1.47/0.56    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.47/0.56    inference(equality_resolution,[],[f94])).
% 1.47/0.56  fof(f94,plain,(
% 1.47/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 1.47/0.56    inference(definition_unfolding,[],[f63,f53])).
% 1.47/0.56  fof(f63,plain,(
% 1.47/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.47/0.56    inference(cnf_transformation,[],[f41])).
% 1.47/0.57  fof(f41,plain,(
% 1.47/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.47/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).
% 1.47/0.57  fof(f40,plain,(
% 1.47/0.57    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f39,plain,(
% 1.47/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.47/0.57    inference(rectify,[],[f38])).
% 1.47/0.57  fof(f38,plain,(
% 1.47/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.47/0.57    inference(flattening,[],[f37])).
% 1.47/0.57  fof(f37,plain,(
% 1.47/0.57    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.47/0.57    inference(nnf_transformation,[],[f2])).
% 1.47/0.57  fof(f2,axiom,(
% 1.47/0.57    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.47/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.47/0.57  fof(f43,plain,(
% 1.47/0.57    sK0 != sK1),
% 1.47/0.57    inference(cnf_transformation,[],[f27])).
% 1.47/0.57  % SZS output end Proof for theBenchmark
% 1.47/0.57  % (28682)------------------------------
% 1.47/0.57  % (28682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (28682)Termination reason: Refutation
% 1.47/0.57  
% 1.47/0.57  % (28682)Memory used [KB]: 2046
% 1.47/0.57  % (28682)Time elapsed: 0.127 s
% 1.47/0.57  % (28682)------------------------------
% 1.47/0.57  % (28682)------------------------------
% 1.47/0.57  % (28676)Success in time 0.196 s
%------------------------------------------------------------------------------
