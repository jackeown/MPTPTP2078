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
% DateTime   : Thu Dec  3 12:38:37 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 432 expanded)
%              Number of leaves         :   17 ( 146 expanded)
%              Depth                    :   15
%              Number of atoms          :  116 ( 497 expanded)
%              Number of equality atoms :   65 ( 421 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f372,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f82,f96,f365])).

fof(f365,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f364,f52])).

fof(f52,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f28,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f47])).

% (338)Refutation not found, incomplete strategy% (338)------------------------------
% (338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f364,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(backward_demodulation,[],[f85,f362])).

fof(f362,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f361,f311])).

fof(f311,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f310,f74])).

fof(f74,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f52,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f32,f48,f48])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f310,plain,(
    ! [X2] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f305,f74])).

fof(f305,plain,(
    ! [X2] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(X2,k1_xboole_0))) ),
    inference(superposition,[],[f56,f284])).

fof(f284,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f93,f151])).

fof(f151,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f68,f74])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0 ),
    inference(unit_resulting_resolution,[],[f53,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f30,f49])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f93,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f90,f52])).

% (335)Termination reason: Refutation not found, incomplete strategy
fof(f90,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(X1,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) ),
    inference(forward_demodulation,[],[f55,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f36,f35,f35,f49])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f37,f49,f35,f49])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f361,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f130,f151])).

fof(f130,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f126,f62])).

fof(f62,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f60,f38])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f126,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f90,f74])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X0,X0)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f56,f38])).

fof(f96,plain,(
    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f51,f54])).

fof(f51,plain,(
    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f27,f49,f50])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f48])).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).

% (335)Memory used [KB]: 6268
% (335)Time elapsed: 0.195 s
% (335)------------------------------
% (335)------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f82,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f26,f26,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f26,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:27:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (327)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.22/0.56  % (325)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.60/0.57  % (328)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.60/0.57  % (353)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.60/0.57  % (336)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.60/0.58  % (332)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.60/0.58  % (330)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.60/0.58  % (325)Refutation not found, incomplete strategy% (325)------------------------------
% 1.60/0.58  % (325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (325)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.58  
% 1.60/0.58  % (325)Memory used [KB]: 1663
% 1.60/0.58  % (325)Time elapsed: 0.149 s
% 1.60/0.58  % (325)------------------------------
% 1.60/0.58  % (325)------------------------------
% 1.60/0.58  % (353)Refutation not found, incomplete strategy% (353)------------------------------
% 1.60/0.58  % (353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (353)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.58  
% 1.60/0.58  % (353)Memory used [KB]: 1663
% 1.60/0.58  % (353)Time elapsed: 0.148 s
% 1.60/0.58  % (353)------------------------------
% 1.60/0.58  % (353)------------------------------
% 1.60/0.58  % (336)Refutation not found, incomplete strategy% (336)------------------------------
% 1.60/0.58  % (336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (336)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.58  
% 1.60/0.58  % (336)Memory used [KB]: 10618
% 1.60/0.58  % (336)Time elapsed: 0.151 s
% 1.60/0.58  % (336)------------------------------
% 1.60/0.58  % (336)------------------------------
% 1.60/0.59  % (329)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.60/0.59  % (349)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.60/0.59  % (341)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.60/0.59  % (349)Refutation not found, incomplete strategy% (349)------------------------------
% 1.60/0.59  % (349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.59  % (349)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.59  
% 1.60/0.59  % (349)Memory used [KB]: 6140
% 1.60/0.59  % (349)Time elapsed: 0.110 s
% 1.60/0.59  % (349)------------------------------
% 1.60/0.59  % (349)------------------------------
% 1.60/0.59  % (334)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.60/0.59  % (339)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.60/0.59  % (326)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.60/0.60  % (334)Refutation not found, incomplete strategy% (334)------------------------------
% 1.60/0.60  % (334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.60  % (347)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.60/0.60  % (334)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.60  
% 1.60/0.60  % (334)Memory used [KB]: 10618
% 1.60/0.60  % (334)Time elapsed: 0.157 s
% 1.60/0.60  % (334)------------------------------
% 1.60/0.60  % (334)------------------------------
% 1.60/0.60  % (324)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.60/0.60  % (352)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.60/0.60  % (341)Refutation not found, incomplete strategy% (341)------------------------------
% 1.60/0.60  % (341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.60  % (341)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.60  
% 1.60/0.60  % (341)Memory used [KB]: 1791
% 1.60/0.60  % (341)Time elapsed: 0.162 s
% 1.60/0.60  % (341)------------------------------
% 1.60/0.60  % (341)------------------------------
% 1.60/0.60  % (352)Refutation not found, incomplete strategy% (352)------------------------------
% 1.60/0.60  % (352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.60  % (352)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.60  
% 1.60/0.60  % (352)Memory used [KB]: 10618
% 1.60/0.60  % (352)Time elapsed: 0.172 s
% 1.60/0.60  % (352)------------------------------
% 1.60/0.60  % (352)------------------------------
% 1.60/0.60  % (333)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.60/0.60  % (350)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.60/0.60  % (345)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.60/0.61  % (351)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.60/0.61  % (342)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.60/0.61  % (344)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.60/0.61  % (343)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.60/0.61  % (335)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.60/0.62  % (338)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.60/0.62  % (348)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.60/0.62  % (337)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.60/0.62  % (351)Refutation not found, incomplete strategy% (351)------------------------------
% 1.60/0.62  % (351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.62  % (351)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.62  
% 1.60/0.62  % (351)Memory used [KB]: 6140
% 1.60/0.62  % (351)Time elapsed: 0.182 s
% 1.60/0.62  % (351)------------------------------
% 1.60/0.62  % (351)------------------------------
% 1.60/0.62  % (331)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.60/0.62  % (346)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.60/0.62  % (340)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.60/0.62  % (350)Refutation not found, incomplete strategy% (350)------------------------------
% 1.60/0.62  % (350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.62  % (342)Refutation not found, incomplete strategy% (342)------------------------------
% 1.60/0.62  % (342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.62  % (350)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.62  
% 1.60/0.62  % (350)Memory used [KB]: 6268
% 1.60/0.62  % (350)Time elapsed: 0.193 s
% 1.60/0.62  % (350)------------------------------
% 1.60/0.62  % (350)------------------------------
% 1.60/0.63  % (328)Refutation found. Thanks to Tanya!
% 1.60/0.63  % SZS status Theorem for theBenchmark
% 1.60/0.63  % (335)Refutation not found, incomplete strategy% (335)------------------------------
% 1.60/0.63  % (335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.63  % (342)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.63  
% 1.60/0.63  % (342)Memory used [KB]: 1663
% 1.60/0.63  % (342)Time elapsed: 0.192 s
% 1.60/0.63  % (342)------------------------------
% 1.60/0.63  % (342)------------------------------
% 1.60/0.63  % SZS output start Proof for theBenchmark
% 1.60/0.63  fof(f372,plain,(
% 1.60/0.63    $false),
% 1.60/0.63    inference(unit_resulting_resolution,[],[f82,f96,f365])).
% 1.60/0.63  fof(f365,plain,(
% 1.60/0.63    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.60/0.63    inference(forward_demodulation,[],[f364,f52])).
% 1.60/0.63  fof(f52,plain,(
% 1.60/0.63    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.60/0.63    inference(definition_unfolding,[],[f28,f49])).
% 1.60/0.63  fof(f49,plain,(
% 1.60/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.60/0.63    inference(definition_unfolding,[],[f34,f48])).
% 1.60/0.63  fof(f48,plain,(
% 1.60/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.60/0.63    inference(definition_unfolding,[],[f33,f47])).
% 1.60/0.63  % (338)Refutation not found, incomplete strategy% (338)------------------------------
% 1.60/0.63  % (338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.63  fof(f47,plain,(
% 1.60/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.60/0.63    inference(definition_unfolding,[],[f42,f46])).
% 1.60/0.63  fof(f46,plain,(
% 1.60/0.63    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.60/0.63    inference(cnf_transformation,[],[f13])).
% 1.60/0.63  fof(f13,axiom,(
% 1.60/0.63    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.60/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.60/0.63  fof(f42,plain,(
% 1.60/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.60/0.63    inference(cnf_transformation,[],[f12])).
% 1.60/0.63  fof(f12,axiom,(
% 1.60/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.60/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.60/0.63  fof(f33,plain,(
% 1.60/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.60/0.63    inference(cnf_transformation,[],[f11])).
% 1.60/0.63  fof(f11,axiom,(
% 1.60/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.60/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.60/0.63  fof(f34,plain,(
% 1.60/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.60/0.63    inference(cnf_transformation,[],[f14])).
% 1.60/0.63  fof(f14,axiom,(
% 1.60/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.60/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.60/0.63  fof(f28,plain,(
% 1.60/0.63    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.60/0.63    inference(cnf_transformation,[],[f4])).
% 1.60/0.63  fof(f4,axiom,(
% 1.60/0.63    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.60/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.60/0.63  fof(f364,plain,(
% 1.60/0.63    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) | ~r1_tarski(X0,X1)) )),
% 1.60/0.63    inference(backward_demodulation,[],[f85,f362])).
% 1.60/0.63  fof(f362,plain,(
% 1.60/0.63    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.60/0.63    inference(forward_demodulation,[],[f361,f311])).
% 1.60/0.63  fof(f311,plain,(
% 1.60/0.63    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.60/0.63    inference(forward_demodulation,[],[f310,f74])).
% 1.60/0.63  fof(f74,plain,(
% 1.60/0.63    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.60/0.63    inference(superposition,[],[f52,f54])).
% 1.60/0.63  fof(f54,plain,(
% 1.60/0.63    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 1.60/0.63    inference(definition_unfolding,[],[f32,f48,f48])).
% 1.60/0.63  fof(f32,plain,(
% 1.60/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.60/0.63    inference(cnf_transformation,[],[f9])).
% 1.60/0.63  fof(f9,axiom,(
% 1.60/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.60/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.60/0.63  fof(f310,plain,(
% 1.60/0.63    ( ! [X2] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)) = k5_xboole_0(X2,k1_xboole_0)) )),
% 1.60/0.63    inference(forward_demodulation,[],[f305,f74])).
% 1.60/0.63  fof(f305,plain,(
% 1.60/0.63    ( ! [X2] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X2)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k5_xboole_0(X2,k1_xboole_0)))) )),
% 1.60/0.63    inference(superposition,[],[f56,f284])).
% 1.60/0.63  fof(f284,plain,(
% 1.60/0.63    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X0,k1_xboole_0)) )),
% 1.60/0.63    inference(backward_demodulation,[],[f93,f151])).
% 1.60/0.63  fof(f151,plain,(
% 1.60/0.63    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3)) )),
% 1.60/0.63    inference(superposition,[],[f68,f74])).
% 1.60/0.63  fof(f68,plain,(
% 1.60/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0) )),
% 1.60/0.63    inference(unit_resulting_resolution,[],[f53,f38])).
% 1.60/0.63  fof(f38,plain,(
% 1.60/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.60/0.63    inference(cnf_transformation,[],[f19])).
% 1.60/0.63  fof(f19,plain,(
% 1.60/0.63    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.60/0.63    inference(ennf_transformation,[],[f5])).
% 1.60/0.63  fof(f5,axiom,(
% 1.60/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.60/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.60/0.63  fof(f53,plain,(
% 1.60/0.63    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.60/0.63    inference(definition_unfolding,[],[f30,f49])).
% 1.60/0.63  fof(f30,plain,(
% 1.60/0.63    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.60/0.63    inference(cnf_transformation,[],[f8])).
% 1.60/0.63  fof(f8,axiom,(
% 1.60/0.63    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.60/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.60/0.63  fof(f93,plain,(
% 1.60/0.63    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.60/0.63    inference(superposition,[],[f90,f52])).
% 1.60/0.63  % (335)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.63  fof(f90,plain,(
% 1.60/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(X1,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))))) )),
% 1.60/0.63    inference(forward_demodulation,[],[f55,f31])).
% 1.60/0.63  fof(f31,plain,(
% 1.60/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.60/0.63    inference(cnf_transformation,[],[f1])).
% 1.60/0.63  fof(f1,axiom,(
% 1.60/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.60/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.60/0.63  fof(f55,plain,(
% 1.60/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 1.60/0.63    inference(definition_unfolding,[],[f36,f35,f35,f49])).
% 1.60/0.63  fof(f35,plain,(
% 1.60/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.60/0.63    inference(cnf_transformation,[],[f3])).
% 1.60/0.63  fof(f3,axiom,(
% 1.60/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.60/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.60/0.63  fof(f36,plain,(
% 1.60/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.60/0.63    inference(cnf_transformation,[],[f7])).
% 1.60/0.63  fof(f7,axiom,(
% 1.60/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.60/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.60/0.63  fof(f56,plain,(
% 1.60/0.63    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.60/0.63    inference(definition_unfolding,[],[f37,f49,f35,f49])).
% 1.60/0.63  fof(f37,plain,(
% 1.60/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.60/0.63    inference(cnf_transformation,[],[f6])).
% 1.60/0.63  fof(f6,axiom,(
% 1.60/0.63    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.60/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.60/0.63  fof(f361,plain,(
% 1.60/0.63    ( ! [X0] : (k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.60/0.63    inference(forward_demodulation,[],[f130,f151])).
% 1.60/0.63  fof(f130,plain,(
% 1.60/0.63    ( ! [X0] : (k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.60/0.63    inference(forward_demodulation,[],[f126,f62])).
% 1.60/0.63  fof(f62,plain,(
% 1.60/0.63    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.60/0.63    inference(unit_resulting_resolution,[],[f60,f38])).
% 1.60/0.63  fof(f60,plain,(
% 1.60/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.60/0.63    inference(equality_resolution,[],[f40])).
% 1.60/0.63  fof(f40,plain,(
% 1.60/0.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.60/0.63    inference(cnf_transformation,[],[f23])).
% 1.60/0.63  fof(f23,plain,(
% 1.60/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.60/0.63    inference(flattening,[],[f22])).
% 1.60/0.63  fof(f22,plain,(
% 1.60/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.60/0.63    inference(nnf_transformation,[],[f2])).
% 1.60/0.63  fof(f2,axiom,(
% 1.60/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.60/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.60/0.63  fof(f126,plain,(
% 1.60/0.63    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.60/0.63    inference(superposition,[],[f90,f74])).
% 1.60/0.63  fof(f85,plain,(
% 1.60/0.63    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X0,X0))) | ~r1_tarski(X0,X1)) )),
% 1.60/0.63    inference(superposition,[],[f56,f38])).
% 1.60/0.63  fof(f96,plain,(
% 1.60/0.63    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.60/0.63    inference(forward_demodulation,[],[f51,f54])).
% 1.60/0.63  fof(f51,plain,(
% 1.60/0.63    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.60/0.63    inference(definition_unfolding,[],[f27,f49,f50])).
% 1.60/0.63  fof(f50,plain,(
% 1.60/0.63    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.60/0.63    inference(definition_unfolding,[],[f29,f48])).
% 1.60/0.63  fof(f29,plain,(
% 1.60/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.60/0.63    inference(cnf_transformation,[],[f10])).
% 1.60/0.63  fof(f10,axiom,(
% 1.60/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.60/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.60/0.63  fof(f27,plain,(
% 1.60/0.63    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.60/0.63    inference(cnf_transformation,[],[f21])).
% 1.60/0.63  fof(f21,plain,(
% 1.60/0.63    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 1.60/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).
% 1.60/0.63  
% 1.60/0.63  % (335)Memory used [KB]: 6268
% 1.60/0.63  % (335)Time elapsed: 0.195 s
% 1.60/0.63  % (335)------------------------------
% 1.60/0.63  % (335)------------------------------
% 1.60/0.63  fof(f20,plain,(
% 1.60/0.63    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 1.60/0.63    introduced(choice_axiom,[])).
% 1.60/0.63  fof(f18,plain,(
% 1.60/0.63    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.60/0.63    inference(ennf_transformation,[],[f17])).
% 1.60/0.63  fof(f17,negated_conjecture,(
% 1.60/0.63    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.60/0.63    inference(negated_conjecture,[],[f16])).
% 1.60/0.63  fof(f16,conjecture,(
% 1.60/0.63    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.60/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.60/0.63  fof(f82,plain,(
% 1.60/0.63    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.60/0.63    inference(unit_resulting_resolution,[],[f26,f26,f57])).
% 1.60/0.63  fof(f57,plain,(
% 1.60/0.63    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.60/0.63    inference(definition_unfolding,[],[f45,f48])).
% 1.60/0.63  fof(f45,plain,(
% 1.60/0.63    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.60/0.63    inference(cnf_transformation,[],[f25])).
% 1.60/0.63  fof(f25,plain,(
% 1.60/0.63    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.60/0.63    inference(flattening,[],[f24])).
% 1.60/0.64  fof(f24,plain,(
% 1.60/0.64    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.60/0.64    inference(nnf_transformation,[],[f15])).
% 1.60/0.64  fof(f15,axiom,(
% 1.60/0.64    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.60/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.60/0.64  fof(f26,plain,(
% 1.60/0.64    r2_hidden(sK0,sK1)),
% 1.60/0.64    inference(cnf_transformation,[],[f21])).
% 1.60/0.64  % SZS output end Proof for theBenchmark
% 1.60/0.64  % (328)------------------------------
% 1.60/0.64  % (328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.64  % (328)Termination reason: Refutation
% 1.60/0.64  
% 1.60/0.64  % (328)Memory used [KB]: 2046
% 1.60/0.64  % (328)Time elapsed: 0.184 s
% 1.60/0.64  % (328)------------------------------
% 1.60/0.64  % (328)------------------------------
% 1.60/0.64  % (323)Success in time 0.265 s
%------------------------------------------------------------------------------
