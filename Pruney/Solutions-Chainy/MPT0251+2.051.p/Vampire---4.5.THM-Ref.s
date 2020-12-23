%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:42 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 202 expanded)
%              Number of leaves         :   18 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  124 ( 270 expanded)
%              Number of equality atoms :   63 ( 193 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f199,plain,(
    $false ),
    inference(subsumption_resolution,[],[f198,f119])).

% (24098)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f119,plain,(
    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f56,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f34,f53,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f56,plain,(
    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f30,f54,f55])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f53])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f53])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f30,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).

% (24102)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
fof(f22,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f198,plain,(
    sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f197,f57])).

fof(f57,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f32,f54])).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f197,plain,(
    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f180,f147])).

fof(f147,plain,(
    ! [X4] : k1_xboole_0 = k5_xboole_0(X4,X4) ),
    inference(forward_demodulation,[],[f146,f78])).

fof(f78,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(resolution,[],[f62,f68])).

fof(f68,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f41,f31])).

fof(f31,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f45,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f146,plain,(
    ! [X4] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X4)) = k5_xboole_0(X4,X4) ),
    inference(forward_demodulation,[],[f140,f69])).

% (24098)Refutation not found, incomplete strategy% (24098)------------------------------
% (24098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24098)Termination reason: Refutation not found, incomplete strategy

% (24098)Memory used [KB]: 1663
% (24098)Time elapsed: 0.173 s
% (24098)------------------------------
% (24098)------------------------------
fof(f69,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f40,f66])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

% (24107)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f24,plain,(
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

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f140,plain,(
    ! [X4] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X4)) = k5_xboole_0(X4,k3_xboole_0(X4,X4)) ),
    inference(superposition,[],[f59,f89])).

% (24102)Refutation not found, incomplete strategy% (24102)------------------------------
% (24102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24102)Termination reason: Refutation not found, incomplete strategy

% (24102)Memory used [KB]: 1663
% (24102)Time elapsed: 0.171 s
% (24102)------------------------------
% (24102)------------------------------
fof(f89,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f57,f58])).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f38,f37,f37,f54])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f180,plain,(
    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f60,f178])).

fof(f178,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f175,f29])).

fof(f29,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f175,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k3_enumset1(sK0,sK0,sK0,sK0,X0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,X0),sK1) ) ),
    inference(resolution,[],[f102,f29])).

fof(f102,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(X11,X10)
      | ~ r2_hidden(X9,X10)
      | k3_enumset1(X11,X11,X11,X11,X9) = k3_xboole_0(k3_enumset1(X11,X11,X11,X11,X9),X10) ) ),
    inference(resolution,[],[f63,f40])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f60,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f39,f54,f37,f54])).

% (24110)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:25:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (24113)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (24085)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (24085)Refutation not found, incomplete strategy% (24085)------------------------------
% 0.21/0.52  % (24085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24085)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24085)Memory used [KB]: 1663
% 0.21/0.52  % (24085)Time elapsed: 0.075 s
% 0.21/0.52  % (24085)------------------------------
% 0.21/0.52  % (24085)------------------------------
% 0.21/0.53  % (24113)Refutation not found, incomplete strategy% (24113)------------------------------
% 0.21/0.53  % (24113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24113)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (24113)Memory used [KB]: 1663
% 0.21/0.53  % (24113)Time elapsed: 0.076 s
% 0.21/0.53  % (24113)------------------------------
% 0.21/0.53  % (24113)------------------------------
% 0.21/0.57  % (24088)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.57  % (24087)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.64/0.58  % (24089)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.64/0.59  % (24084)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.64/0.59  % (24086)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.64/0.59  % (24099)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.64/0.59  % (24096)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.64/0.59  % (24093)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.64/0.59  % (24096)Refutation not found, incomplete strategy% (24096)------------------------------
% 1.64/0.59  % (24096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (24096)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.59  
% 1.64/0.59  % (24096)Memory used [KB]: 10618
% 1.64/0.59  % (24096)Time elapsed: 0.165 s
% 1.64/0.59  % (24096)------------------------------
% 1.64/0.59  % (24096)------------------------------
% 1.81/0.59  % (24090)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.81/0.60  % (24111)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.81/0.60  % (24111)Refutation not found, incomplete strategy% (24111)------------------------------
% 1.81/0.60  % (24111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.60  % (24111)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.60  
% 1.81/0.60  % (24111)Memory used [KB]: 6140
% 1.81/0.60  % (24111)Time elapsed: 0.162 s
% 1.81/0.60  % (24111)------------------------------
% 1.81/0.60  % (24111)------------------------------
% 1.81/0.60  % (24106)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.81/0.60  % (24090)Refutation found. Thanks to Tanya!
% 1.81/0.60  % SZS status Theorem for theBenchmark
% 1.81/0.60  % (24095)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.81/0.60  % (24108)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.81/0.60  % (24100)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.81/0.60  % (24141)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.81/0.60  % (24108)Refutation not found, incomplete strategy% (24108)------------------------------
% 1.81/0.60  % (24108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.60  % (24108)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.60  
% 1.81/0.60  % (24108)Memory used [KB]: 10618
% 1.81/0.60  % (24108)Time elapsed: 0.174 s
% 1.81/0.60  % (24108)------------------------------
% 1.81/0.60  % (24108)------------------------------
% 1.81/0.60  % (24109)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.81/0.61  % SZS output start Proof for theBenchmark
% 1.81/0.61  fof(f199,plain,(
% 1.81/0.61    $false),
% 1.81/0.61    inference(subsumption_resolution,[],[f198,f119])).
% 1.81/0.61  % (24098)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.81/0.61  fof(f119,plain,(
% 1.81/0.61    sK1 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.81/0.61    inference(forward_demodulation,[],[f56,f58])).
% 1.81/0.61  fof(f58,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 1.81/0.61    inference(definition_unfolding,[],[f34,f53,f53])).
% 1.81/0.61  fof(f53,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.81/0.61    inference(definition_unfolding,[],[f36,f52])).
% 1.81/0.61  fof(f52,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.81/0.61    inference(definition_unfolding,[],[f47,f51])).
% 1.81/0.61  fof(f51,plain,(
% 1.81/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f14])).
% 1.81/0.61  fof(f14,axiom,(
% 1.81/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.81/0.61  fof(f47,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f13])).
% 1.81/0.61  fof(f13,axiom,(
% 1.81/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.81/0.61  fof(f36,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f12])).
% 1.81/0.61  fof(f12,axiom,(
% 1.81/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.81/0.61  fof(f34,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f10])).
% 1.81/0.61  fof(f10,axiom,(
% 1.81/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.81/0.61  fof(f56,plain,(
% 1.81/0.61    sK1 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.81/0.61    inference(definition_unfolding,[],[f30,f54,f55])).
% 1.81/0.61  fof(f55,plain,(
% 1.81/0.61    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.81/0.61    inference(definition_unfolding,[],[f33,f53])).
% 1.81/0.61  fof(f33,plain,(
% 1.81/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f11])).
% 1.81/0.61  fof(f11,axiom,(
% 1.81/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.81/0.61  fof(f54,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.81/0.61    inference(definition_unfolding,[],[f35,f53])).
% 1.81/0.61  fof(f35,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.81/0.61    inference(cnf_transformation,[],[f15])).
% 1.81/0.61  fof(f15,axiom,(
% 1.81/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.81/0.61  fof(f30,plain,(
% 1.81/0.61    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.81/0.61    inference(cnf_transformation,[],[f23])).
% 1.81/0.61  fof(f23,plain,(
% 1.81/0.61    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 1.81/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).
% 1.81/0.61  % (24102)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.81/0.61  fof(f22,plain,(
% 1.81/0.61    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 1.81/0.61    introduced(choice_axiom,[])).
% 1.81/0.61  fof(f19,plain,(
% 1.81/0.61    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.81/0.61    inference(ennf_transformation,[],[f18])).
% 1.81/0.61  fof(f18,negated_conjecture,(
% 1.81/0.61    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.81/0.61    inference(negated_conjecture,[],[f17])).
% 1.81/0.61  fof(f17,conjecture,(
% 1.81/0.61    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.81/0.61  fof(f198,plain,(
% 1.81/0.61    sK1 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.81/0.61    inference(forward_demodulation,[],[f197,f57])).
% 1.81/0.61  fof(f57,plain,(
% 1.81/0.61    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.81/0.61    inference(definition_unfolding,[],[f32,f54])).
% 1.81/0.61  fof(f32,plain,(
% 1.81/0.61    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.81/0.61    inference(cnf_transformation,[],[f4])).
% 1.81/0.61  fof(f4,axiom,(
% 1.81/0.61    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.81/0.61  fof(f197,plain,(
% 1.81/0.61    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0))),
% 1.81/0.61    inference(forward_demodulation,[],[f180,f147])).
% 1.81/0.61  fof(f147,plain,(
% 1.81/0.61    ( ! [X4] : (k1_xboole_0 = k5_xboole_0(X4,X4)) )),
% 1.81/0.61    inference(forward_demodulation,[],[f146,f78])).
% 1.81/0.61  fof(f78,plain,(
% 1.81/0.61    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) )),
% 1.81/0.61    inference(resolution,[],[f62,f68])).
% 1.81/0.61  fof(f68,plain,(
% 1.81/0.61    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.81/0.61    inference(resolution,[],[f41,f31])).
% 1.81/0.61  fof(f31,plain,(
% 1.81/0.61    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f8])).
% 1.81/0.61  fof(f8,axiom,(
% 1.81/0.61    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.81/0.61  fof(f41,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f21])).
% 1.81/0.61  fof(f21,plain,(
% 1.81/0.61    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.81/0.61    inference(ennf_transformation,[],[f1])).
% 1.81/0.61  fof(f1,axiom,(
% 1.81/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.81/0.61  fof(f62,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.81/0.61    inference(definition_unfolding,[],[f45,f37])).
% 1.81/0.61  fof(f37,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.81/0.61    inference(cnf_transformation,[],[f3])).
% 1.81/0.61  fof(f3,axiom,(
% 1.81/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.81/0.61  fof(f45,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f26])).
% 1.81/0.61  fof(f26,plain,(
% 1.81/0.61    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.81/0.61    inference(nnf_transformation,[],[f9])).
% 1.81/0.61  fof(f9,axiom,(
% 1.81/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.81/0.61  fof(f146,plain,(
% 1.81/0.61    ( ! [X4] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X4)) = k5_xboole_0(X4,X4)) )),
% 1.81/0.61    inference(forward_demodulation,[],[f140,f69])).
% 1.81/0.61  % (24098)Refutation not found, incomplete strategy% (24098)------------------------------
% 1.81/0.61  % (24098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.61  % (24098)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.61  
% 1.81/0.61  % (24098)Memory used [KB]: 1663
% 1.81/0.61  % (24098)Time elapsed: 0.173 s
% 1.81/0.61  % (24098)------------------------------
% 1.81/0.61  % (24098)------------------------------
% 1.81/0.61  fof(f69,plain,(
% 1.81/0.61    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.81/0.61    inference(resolution,[],[f40,f66])).
% 1.81/0.61  fof(f66,plain,(
% 1.81/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.81/0.61    inference(equality_resolution,[],[f43])).
% 1.81/0.61  fof(f43,plain,(
% 1.81/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.81/0.61    inference(cnf_transformation,[],[f25])).
% 1.81/0.61  fof(f25,plain,(
% 1.81/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/0.61    inference(flattening,[],[f24])).
% 1.81/0.61  % (24107)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.81/0.61  fof(f24,plain,(
% 1.81/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/0.61    inference(nnf_transformation,[],[f2])).
% 1.81/0.61  fof(f2,axiom,(
% 1.81/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.81/0.61  fof(f40,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.81/0.61    inference(cnf_transformation,[],[f20])).
% 1.81/0.61  fof(f20,plain,(
% 1.81/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.81/0.61    inference(ennf_transformation,[],[f5])).
% 1.81/0.61  fof(f5,axiom,(
% 1.81/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.81/0.61  fof(f140,plain,(
% 1.81/0.61    ( ! [X4] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X4)) = k5_xboole_0(X4,k3_xboole_0(X4,X4))) )),
% 1.81/0.61    inference(superposition,[],[f59,f89])).
% 1.81/0.61  % (24102)Refutation not found, incomplete strategy% (24102)------------------------------
% 1.81/0.61  % (24102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.61  % (24102)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.61  
% 1.81/0.61  % (24102)Memory used [KB]: 1663
% 1.81/0.61  % (24102)Time elapsed: 0.171 s
% 1.81/0.61  % (24102)------------------------------
% 1.81/0.61  % (24102)------------------------------
% 1.81/0.61  fof(f89,plain,(
% 1.81/0.61    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.81/0.61    inference(superposition,[],[f57,f58])).
% 1.81/0.61  fof(f59,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 1.81/0.61    inference(definition_unfolding,[],[f38,f37,f37,f54])).
% 1.81/0.61  fof(f38,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f7])).
% 1.81/0.61  fof(f7,axiom,(
% 1.81/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.81/0.61  fof(f180,plain,(
% 1.81/0.61    k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))))),
% 1.81/0.61    inference(superposition,[],[f60,f178])).
% 1.81/0.61  fof(f178,plain,(
% 1.81/0.61    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.81/0.61    inference(resolution,[],[f175,f29])).
% 1.81/0.61  fof(f29,plain,(
% 1.81/0.61    r2_hidden(sK0,sK1)),
% 1.81/0.61    inference(cnf_transformation,[],[f23])).
% 1.81/0.61  fof(f175,plain,(
% 1.81/0.61    ( ! [X0] : (~r2_hidden(X0,sK1) | k3_enumset1(sK0,sK0,sK0,sK0,X0) = k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,X0),sK1)) )),
% 1.81/0.61    inference(resolution,[],[f102,f29])).
% 1.81/0.61  fof(f102,plain,(
% 1.81/0.61    ( ! [X10,X11,X9] : (~r2_hidden(X11,X10) | ~r2_hidden(X9,X10) | k3_enumset1(X11,X11,X11,X11,X9) = k3_xboole_0(k3_enumset1(X11,X11,X11,X11,X9),X10)) )),
% 1.81/0.61    inference(resolution,[],[f63,f40])).
% 1.81/0.61  fof(f63,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.81/0.61    inference(definition_unfolding,[],[f50,f53])).
% 1.81/0.61  fof(f50,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f28])).
% 1.81/0.61  fof(f28,plain,(
% 1.81/0.61    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.81/0.61    inference(flattening,[],[f27])).
% 1.81/0.61  fof(f27,plain,(
% 1.81/0.61    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.81/0.61    inference(nnf_transformation,[],[f16])).
% 1.81/0.61  fof(f16,axiom,(
% 1.81/0.61    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.81/0.61  fof(f60,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.81/0.61    inference(definition_unfolding,[],[f39,f54,f37,f54])).
% 1.81/0.61  % (24110)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.81/0.61  fof(f39,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f6])).
% 1.81/0.61  fof(f6,axiom,(
% 1.81/0.61    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.81/0.61  % SZS output end Proof for theBenchmark
% 1.81/0.61  % (24090)------------------------------
% 1.81/0.61  % (24090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.61  % (24090)Termination reason: Refutation
% 1.81/0.61  
% 1.81/0.61  % (24090)Memory used [KB]: 10746
% 1.81/0.61  % (24090)Time elapsed: 0.164 s
% 1.81/0.61  % (24090)------------------------------
% 1.81/0.61  % (24090)------------------------------
% 1.81/0.61  % (24104)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.81/0.61  % (24142)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.81/0.61  % (24095)Refutation not found, incomplete strategy% (24095)------------------------------
% 1.81/0.61  % (24095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.61  % (24095)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.61  
% 1.81/0.61  % (24095)Memory used [KB]: 6268
% 1.81/0.61  % (24095)Time elapsed: 0.176 s
% 1.81/0.61  % (24095)------------------------------
% 1.81/0.61  % (24095)------------------------------
% 1.81/0.61  % (24094)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.81/0.61  % (24110)Refutation not found, incomplete strategy% (24110)------------------------------
% 1.81/0.61  % (24110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.61  % (24110)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.61  
% 1.81/0.61  % (24110)Memory used [KB]: 6268
% 1.81/0.61  % (24110)Time elapsed: 0.182 s
% 1.81/0.61  % (24110)------------------------------
% 1.81/0.61  % (24110)------------------------------
% 1.81/0.61  % (24083)Success in time 0.242 s
%------------------------------------------------------------------------------
