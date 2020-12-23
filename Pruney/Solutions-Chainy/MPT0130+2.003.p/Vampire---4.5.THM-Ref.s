%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:03 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 134 expanded)
%              Number of leaves         :   11 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  104 ( 307 expanded)
%              Number of equality atoms :   47 ( 118 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(subsumption_resolution,[],[f153,f142])).

fof(f142,plain,(
    ! [X4,X2,X3] : k2_xboole_0(k2_xboole_0(X4,X3),X2) = k2_xboole_0(X4,k2_xboole_0(X3,X2)) ),
    inference(backward_demodulation,[],[f100,f140])).

fof(f140,plain,(
    ! [X2,X3] : k2_xboole_0(X3,X2) = k2_xboole_0(k2_xboole_0(X3,X2),X2) ),
    inference(backward_demodulation,[],[f62,f134])).

% (10552)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f134,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(resolution,[],[f128,f27])).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k2_xboole_0(X0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f127,f46])).

fof(f46,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f127,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0)
      | k2_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f41,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,sK4(X0,X1,X2))
      | k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ( ~ r1_tarski(X1,sK4(X0,X1,X2))
        & r1_tarski(X2,sK4(X0,X1,X2))
        & r1_tarski(X0,sK4(X0,X1,X2)) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f24])).

% (10571)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% (10558)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% (10571)Refutation not found, incomplete strategy% (10571)------------------------------
% (10571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10571)Termination reason: Refutation not found, incomplete strategy

% (10571)Memory used [KB]: 6140
% (10571)Time elapsed: 0.181 s
% (10571)------------------------------
% (10571)------------------------------
% (10558)Refutation not found, incomplete strategy% (10558)------------------------------
% (10558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10558)Termination reason: Refutation not found, incomplete strategy

% (10558)Memory used [KB]: 1663
% (10558)Time elapsed: 0.181 s
% (10558)------------------------------
% (10558)------------------------------
% (10557)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% (10570)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% (10570)Refutation not found, incomplete strategy% (10570)------------------------------
% (10570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10570)Termination reason: Refutation not found, incomplete strategy

% (10570)Memory used [KB]: 6140
% (10570)Time elapsed: 0.182 s
% (10570)------------------------------
% (10570)------------------------------
% (10568)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% (10560)Refutation not found, incomplete strategy% (10560)------------------------------
% (10560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10560)Termination reason: Refutation not found, incomplete strategy

% (10560)Memory used [KB]: 10618
% (10560)Time elapsed: 0.194 s
% (10560)------------------------------
% (10560)------------------------------
% (10568)Refutation not found, incomplete strategy% (10568)------------------------------
% (10568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10568)Termination reason: Refutation not found, incomplete strategy

% (10568)Memory used [KB]: 10618
% (10568)Time elapsed: 0.195 s
% (10568)------------------------------
% (10568)------------------------------
fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
     => ( ~ r1_tarski(X1,sK4(X0,X1,X2))
        & r1_tarski(X2,sK4(X0,X1,X2))
        & r1_tarski(X0,sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) = X1
      | ? [X3] :
          ( ~ r1_tarski(X1,X3)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X3) )
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,sK4(X0,X1,X2))
      | k2_xboole_0(X0,X2) = X1
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X2,X3] : k2_xboole_0(k2_xboole_0(X3,k1_xboole_0),X2) = k2_xboole_0(k2_xboole_0(X3,X2),X2) ),
    inference(superposition,[],[f38,f49])).

fof(f49,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f31,f27])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_1)).

fof(f100,plain,(
    ! [X4,X2,X3] : k2_xboole_0(k2_xboole_0(X4,X3),X2) = k2_xboole_0(k2_xboole_0(X4,k2_xboole_0(X3,X2)),k2_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f97,f38])).

fof(f97,plain,(
    ! [X4,X2,X3] : k2_xboole_0(k2_xboole_0(X4,X2),k2_xboole_0(X3,X2)) = k2_xboole_0(k2_xboole_0(X4,k2_xboole_0(X3,X2)),k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f38,f67])).

fof(f67,plain,(
    ! [X2,X3] : k2_xboole_0(X3,X2) = k2_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f60,f49])).

fof(f60,plain,(
    ! [X2,X3] : k2_xboole_0(k2_xboole_0(k1_xboole_0,X3),X2) = k2_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f38,f49])).

fof(f153,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3)) ),
    inference(backward_demodulation,[],[f45,f142])).

fof(f45,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3)) ),
    inference(definition_unfolding,[],[f26,f44,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f37,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3))) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f26,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:30:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (10545)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (10545)Refutation not found, incomplete strategy% (10545)------------------------------
% 0.21/0.55  % (10545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10546)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.55  % (10545)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10545)Memory used [KB]: 1663
% 0.21/0.55  % (10545)Time elapsed: 0.123 s
% 0.21/0.55  % (10545)------------------------------
% 0.21/0.55  % (10545)------------------------------
% 0.21/0.56  % (10561)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (10562)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (10561)Refutation not found, incomplete strategy% (10561)------------------------------
% 0.21/0.56  % (10561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10561)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (10561)Memory used [KB]: 1663
% 0.21/0.56  % (10561)Time elapsed: 0.136 s
% 0.21/0.56  % (10561)------------------------------
% 0.21/0.56  % (10561)------------------------------
% 0.21/0.56  % (10554)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (10554)Refutation not found, incomplete strategy% (10554)------------------------------
% 0.21/0.56  % (10554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10562)Refutation not found, incomplete strategy% (10562)------------------------------
% 0.21/0.56  % (10562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10562)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (10562)Memory used [KB]: 1663
% 0.21/0.56  % (10562)Time elapsed: 0.131 s
% 0.21/0.56  % (10562)------------------------------
% 0.21/0.56  % (10562)------------------------------
% 0.21/0.56  % (10556)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (10554)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (10554)Memory used [KB]: 10746
% 0.21/0.56  % (10554)Time elapsed: 0.134 s
% 0.21/0.56  % (10554)------------------------------
% 0.21/0.56  % (10554)------------------------------
% 0.21/0.57  % (10549)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.57  % (10572)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.57  % (10572)Refutation not found, incomplete strategy% (10572)------------------------------
% 0.21/0.57  % (10572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (10572)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (10572)Memory used [KB]: 10746
% 0.21/0.57  % (10572)Time elapsed: 0.143 s
% 0.21/0.57  % (10572)------------------------------
% 0.21/0.57  % (10572)------------------------------
% 0.21/0.57  % (10547)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.57  % (10550)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (10559)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.58  % (10555)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.58  % (10553)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.58  % (10555)Refutation not found, incomplete strategy% (10555)------------------------------
% 0.21/0.58  % (10555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (10555)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (10555)Memory used [KB]: 6140
% 0.21/0.58  % (10555)Time elapsed: 0.153 s
% 0.21/0.58  % (10555)------------------------------
% 0.21/0.58  % (10555)------------------------------
% 0.21/0.58  % (10544)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.59  % (10551)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.59  % (10556)Refutation not found, incomplete strategy% (10556)------------------------------
% 0.21/0.59  % (10556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (10556)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (10556)Memory used [KB]: 10618
% 0.21/0.59  % (10556)Time elapsed: 0.165 s
% 0.21/0.59  % (10556)------------------------------
% 0.21/0.59  % (10556)------------------------------
% 0.21/0.59  % (10567)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.59  % (10548)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.66/0.59  % (10560)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.66/0.60  % (10573)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.66/0.60  % (10566)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.66/0.60  % (10573)Refutation not found, incomplete strategy% (10573)------------------------------
% 1.66/0.60  % (10573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.60  % (10573)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.60  
% 1.66/0.60  % (10573)Memory used [KB]: 1663
% 1.66/0.60  % (10573)Time elapsed: 0.002 s
% 1.66/0.60  % (10573)------------------------------
% 1.66/0.60  % (10573)------------------------------
% 1.66/0.60  % (10565)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.66/0.60  % (10566)Refutation found. Thanks to Tanya!
% 1.66/0.60  % SZS status Theorem for theBenchmark
% 1.66/0.60  % SZS output start Proof for theBenchmark
% 1.66/0.60  fof(f159,plain,(
% 1.66/0.60    $false),
% 1.66/0.60    inference(subsumption_resolution,[],[f153,f142])).
% 1.66/0.60  fof(f142,plain,(
% 1.66/0.60    ( ! [X4,X2,X3] : (k2_xboole_0(k2_xboole_0(X4,X3),X2) = k2_xboole_0(X4,k2_xboole_0(X3,X2))) )),
% 1.66/0.60    inference(backward_demodulation,[],[f100,f140])).
% 1.66/0.60  fof(f140,plain,(
% 1.66/0.60    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = k2_xboole_0(k2_xboole_0(X3,X2),X2)) )),
% 1.66/0.60    inference(backward_demodulation,[],[f62,f134])).
% 1.66/0.60  % (10552)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.66/0.60  fof(f134,plain,(
% 1.66/0.60    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.66/0.60    inference(resolution,[],[f128,f27])).
% 1.66/0.60  fof(f27,plain,(
% 1.66/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f6])).
% 1.66/0.60  fof(f6,axiom,(
% 1.66/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.66/0.60  fof(f128,plain,(
% 1.66/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k2_xboole_0(X0,X1) = X0) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f127,f46])).
% 1.66/0.60  fof(f46,plain,(
% 1.66/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.66/0.60    inference(equality_resolution,[],[f33])).
% 1.66/0.60  fof(f33,plain,(
% 1.66/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.66/0.60    inference(cnf_transformation,[],[f22])).
% 1.66/0.60  fof(f22,plain,(
% 1.66/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.66/0.60    inference(flattening,[],[f21])).
% 1.66/0.60  fof(f21,plain,(
% 1.66/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.66/0.60    inference(nnf_transformation,[],[f2])).
% 1.66/0.60  fof(f2,axiom,(
% 1.66/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.66/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.66/0.60  fof(f127,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 1.66/0.60    inference(duplicate_literal_removal,[],[f122])).
% 1.66/0.60  fof(f122,plain,(
% 1.66/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0) | k2_xboole_0(X0,X1) = X0 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0)) )),
% 1.66/0.60    inference(resolution,[],[f41,f39])).
% 1.66/0.60  fof(f39,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,sK4(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f25])).
% 1.66/0.60  fof(f25,plain,(
% 1.66/0.60    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (~r1_tarski(X1,sK4(X0,X1,X2)) & r1_tarski(X2,sK4(X0,X1,X2)) & r1_tarski(X0,sK4(X0,X1,X2))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.66/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f24])).
% 1.66/0.61  % (10571)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.66/0.61  % (10558)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.88/0.61  % (10571)Refutation not found, incomplete strategy% (10571)------------------------------
% 1.88/0.61  % (10571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.61  % (10571)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.61  
% 1.88/0.61  % (10571)Memory used [KB]: 6140
% 1.88/0.61  % (10571)Time elapsed: 0.181 s
% 1.88/0.61  % (10571)------------------------------
% 1.88/0.61  % (10571)------------------------------
% 1.88/0.61  % (10558)Refutation not found, incomplete strategy% (10558)------------------------------
% 1.88/0.61  % (10558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.61  % (10558)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.61  
% 1.88/0.61  % (10558)Memory used [KB]: 1663
% 1.88/0.61  % (10558)Time elapsed: 0.181 s
% 1.88/0.61  % (10558)------------------------------
% 1.88/0.61  % (10558)------------------------------
% 1.88/0.61  % (10557)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.88/0.61  % (10570)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.88/0.61  % (10570)Refutation not found, incomplete strategy% (10570)------------------------------
% 1.88/0.61  % (10570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.61  % (10570)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.61  
% 1.88/0.61  % (10570)Memory used [KB]: 6140
% 1.88/0.61  % (10570)Time elapsed: 0.182 s
% 1.88/0.61  % (10570)------------------------------
% 1.88/0.61  % (10570)------------------------------
% 1.88/0.62  % (10568)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.88/0.62  % (10560)Refutation not found, incomplete strategy% (10560)------------------------------
% 1.88/0.62  % (10560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.62  % (10560)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.62  
% 1.88/0.62  % (10560)Memory used [KB]: 10618
% 1.88/0.62  % (10560)Time elapsed: 0.194 s
% 1.88/0.62  % (10560)------------------------------
% 1.88/0.62  % (10560)------------------------------
% 1.88/0.62  % (10568)Refutation not found, incomplete strategy% (10568)------------------------------
% 1.88/0.62  % (10568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.62  % (10568)Termination reason: Refutation not found, incomplete strategy
% 1.88/0.62  
% 1.88/0.62  % (10568)Memory used [KB]: 10618
% 1.88/0.62  % (10568)Time elapsed: 0.195 s
% 1.88/0.62  % (10568)------------------------------
% 1.88/0.62  % (10568)------------------------------
% 1.88/0.62  fof(f24,plain,(
% 1.88/0.62    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) => (~r1_tarski(X1,sK4(X0,X1,X2)) & r1_tarski(X2,sK4(X0,X1,X2)) & r1_tarski(X0,sK4(X0,X1,X2))))),
% 1.88/0.62    introduced(choice_axiom,[])).
% 1.88/0.62  fof(f18,plain,(
% 1.88/0.62    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | ? [X3] : (~r1_tarski(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X3)) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.88/0.62    inference(flattening,[],[f17])).
% 1.88/0.62  fof(f17,plain,(
% 1.88/0.62    ! [X0,X1,X2] : (k2_xboole_0(X0,X2) = X1 | (? [X3] : (~r1_tarski(X1,X3) & (r1_tarski(X2,X3) & r1_tarski(X0,X3))) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.88/0.62    inference(ennf_transformation,[],[f5])).
% 1.88/0.62  fof(f5,axiom,(
% 1.88/0.62    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 1.88/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).
% 1.88/0.62  fof(f41,plain,(
% 1.88/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X1,sK4(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.88/0.62    inference(cnf_transformation,[],[f25])).
% 1.88/0.62  fof(f62,plain,(
% 1.88/0.62    ( ! [X2,X3] : (k2_xboole_0(k2_xboole_0(X3,k1_xboole_0),X2) = k2_xboole_0(k2_xboole_0(X3,X2),X2)) )),
% 1.88/0.62    inference(superposition,[],[f38,f49])).
% 1.88/0.62  fof(f49,plain,(
% 1.88/0.62    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.88/0.62    inference(resolution,[],[f31,f27])).
% 1.88/0.62  fof(f31,plain,(
% 1.88/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.88/0.62    inference(cnf_transformation,[],[f16])).
% 1.88/0.62  fof(f16,plain,(
% 1.88/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.88/0.62    inference(ennf_transformation,[],[f4])).
% 1.88/0.62  fof(f4,axiom,(
% 1.88/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.88/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.88/0.62  fof(f38,plain,(
% 1.88/0.62    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))) )),
% 1.88/0.62    inference(cnf_transformation,[],[f8])).
% 1.88/0.62  fof(f8,axiom,(
% 1.88/0.62    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))),
% 1.88/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_1)).
% 1.88/0.62  fof(f100,plain,(
% 1.88/0.62    ( ! [X4,X2,X3] : (k2_xboole_0(k2_xboole_0(X4,X3),X2) = k2_xboole_0(k2_xboole_0(X4,k2_xboole_0(X3,X2)),k2_xboole_0(X3,X2))) )),
% 1.88/0.62    inference(forward_demodulation,[],[f97,f38])).
% 1.88/0.62  fof(f97,plain,(
% 1.88/0.62    ( ! [X4,X2,X3] : (k2_xboole_0(k2_xboole_0(X4,X2),k2_xboole_0(X3,X2)) = k2_xboole_0(k2_xboole_0(X4,k2_xboole_0(X3,X2)),k2_xboole_0(X3,X2))) )),
% 1.88/0.62    inference(superposition,[],[f38,f67])).
% 1.88/0.62  fof(f67,plain,(
% 1.88/0.62    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = k2_xboole_0(X2,k2_xboole_0(X3,X2))) )),
% 1.88/0.62    inference(forward_demodulation,[],[f60,f49])).
% 1.88/0.62  fof(f60,plain,(
% 1.88/0.62    ( ! [X2,X3] : (k2_xboole_0(k2_xboole_0(k1_xboole_0,X3),X2) = k2_xboole_0(X2,k2_xboole_0(X3,X2))) )),
% 1.88/0.62    inference(superposition,[],[f38,f49])).
% 1.88/0.62  fof(f153,plain,(
% 1.88/0.62    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),k1_tarski(sK3))),
% 1.88/0.62    inference(backward_demodulation,[],[f45,f142])).
% 1.88/0.62  fof(f45,plain,(
% 1.88/0.62    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)),k1_tarski(sK3))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK3))),
% 1.88/0.62    inference(definition_unfolding,[],[f26,f44,f43])).
% 1.88/0.62  fof(f43,plain,(
% 1.88/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2))) )),
% 1.88/0.62    inference(definition_unfolding,[],[f37,f30])).
% 1.88/0.62  fof(f30,plain,(
% 1.88/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.88/0.62    inference(cnf_transformation,[],[f9])).
% 1.88/0.62  fof(f9,axiom,(
% 1.88/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.88/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 1.88/0.62  fof(f37,plain,(
% 1.88/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.88/0.62    inference(cnf_transformation,[],[f10])).
% 1.88/0.62  fof(f10,axiom,(
% 1.88/0.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 1.88/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 1.88/0.62  fof(f44,plain,(
% 1.88/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)))) )),
% 1.88/0.62    inference(definition_unfolding,[],[f42,f43])).
% 1.88/0.62  fof(f42,plain,(
% 1.88/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 1.88/0.62    inference(cnf_transformation,[],[f11])).
% 1.88/0.62  fof(f11,axiom,(
% 1.88/0.62    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 1.88/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 1.88/0.62  fof(f26,plain,(
% 1.88/0.62    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3))),
% 1.88/0.62    inference(cnf_transformation,[],[f20])).
% 1.88/0.62  fof(f20,plain,(
% 1.88/0.62    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3))),
% 1.88/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f19])).
% 1.88/0.62  fof(f19,plain,(
% 1.88/0.62    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_tarski(sK3))),
% 1.88/0.62    introduced(choice_axiom,[])).
% 1.88/0.62  fof(f15,plain,(
% 1.88/0.62    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.88/0.62    inference(ennf_transformation,[],[f13])).
% 1.88/0.62  fof(f13,negated_conjecture,(
% 1.88/0.62    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.88/0.62    inference(negated_conjecture,[],[f12])).
% 1.88/0.62  fof(f12,conjecture,(
% 1.88/0.62    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.88/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 1.88/0.62  % SZS output end Proof for theBenchmark
% 1.88/0.62  % (10566)------------------------------
% 1.88/0.62  % (10566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.88/0.62  % (10566)Termination reason: Refutation
% 1.88/0.62  
% 1.88/0.62  % (10566)Memory used [KB]: 6268
% 1.88/0.62  % (10566)Time elapsed: 0.181 s
% 1.88/0.62  % (10566)------------------------------
% 1.88/0.62  % (10566)------------------------------
% 1.88/0.62  % (10543)Success in time 0.244 s
%------------------------------------------------------------------------------
