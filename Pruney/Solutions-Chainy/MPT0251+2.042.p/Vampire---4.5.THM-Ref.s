%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:40 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 491 expanded)
%              Number of leaves         :   17 ( 164 expanded)
%              Depth                    :   20
%              Number of atoms          :  127 ( 576 expanded)
%              Number of equality atoms :   65 ( 468 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f545,plain,(
    $false ),
    inference(subsumption_resolution,[],[f544,f40])).

fof(f40,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK2 != k2_xboole_0(k1_tarski(sK1),sK2)
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK2 != k2_xboole_0(k1_tarski(sK1),sK2)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f544,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f541])).

fof(f541,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f540,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f69,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f540,plain,(
    ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) ),
    inference(trivial_inequality_removal,[],[f537])).

fof(f537,plain,
    ( sK2 != sK2
    | ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) ),
    inference(superposition,[],[f120,f465])).

fof(f465,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f464,f76])).

fof(f76,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f42,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f72])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f464,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f165,f255])).

fof(f255,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(subsumption_resolution,[],[f247,f86])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f247,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f242,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f242,plain,(
    ! [X6] : k1_xboole_0 = k5_xboole_0(X6,k3_xboole_0(X6,X6)) ),
    inference(forward_demodulation,[],[f241,f202])).

fof(f202,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f195,f153])).

fof(f153,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f141,f139])).

fof(f139,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(superposition,[],[f121,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f46,f73])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f121,plain,(
    ! [X2,X1] : r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(superposition,[],[f77,f78])).

fof(f78,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f45,f72,f72])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f44,f73])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f141,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f138,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f138,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f121,f76])).

fof(f195,plain,(
    ! [X1] : k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(forward_demodulation,[],[f189,f126])).

fof(f126,plain,(
    ! [X15] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X15)) = X15 ),
    inference(superposition,[],[f76,f78])).

fof(f189,plain,(
    ! [X1] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f126,f81])).

fof(f81,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f51,f73,f49,f73])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f241,plain,(
    ! [X6] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X6,k3_xboole_0(X6,X6)) ),
    inference(forward_demodulation,[],[f230,f153])).

fof(f230,plain,(
    ! [X6] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X6)) = k5_xboole_0(X6,k3_xboole_0(X6,X6)) ),
    inference(superposition,[],[f80,f126])).

fof(f80,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f50,f49,f49,f73])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f165,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X0,X0)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f81,f53])).

fof(f120,plain,(
    sK2 != k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(backward_demodulation,[],[f75,f78])).

fof(f75,plain,(
    sK2 != k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)) ),
    inference(definition_unfolding,[],[f41,f73,f74])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f72])).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (19755)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.48  % (19771)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (19751)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (19750)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (19748)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (19747)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (19766)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (19763)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (19749)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (19752)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (19769)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (19760)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (19758)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (19761)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (19774)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (19775)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (19765)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (19764)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (19762)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (19768)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (19776)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (19754)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (19756)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (19773)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (19757)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (19757)Refutation not found, incomplete strategy% (19757)------------------------------
% 0.21/0.54  % (19757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19757)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (19757)Memory used [KB]: 10618
% 0.21/0.54  % (19757)Time elapsed: 0.139 s
% 0.21/0.54  % (19757)------------------------------
% 0.21/0.54  % (19757)------------------------------
% 0.21/0.54  % (19767)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (19769)Refutation not found, incomplete strategy% (19769)------------------------------
% 0.21/0.54  % (19769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19769)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (19769)Memory used [KB]: 10746
% 0.21/0.54  % (19769)Time elapsed: 0.102 s
% 0.21/0.54  % (19769)------------------------------
% 0.21/0.54  % (19769)------------------------------
% 0.21/0.54  % (19772)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (19753)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (19759)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (19770)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.60/0.58  % (19774)Refutation found. Thanks to Tanya!
% 1.60/0.58  % SZS status Theorem for theBenchmark
% 1.60/0.58  % SZS output start Proof for theBenchmark
% 1.60/0.58  fof(f545,plain,(
% 1.60/0.58    $false),
% 1.60/0.58    inference(subsumption_resolution,[],[f544,f40])).
% 1.60/0.58  fof(f40,plain,(
% 1.60/0.58    r2_hidden(sK1,sK2)),
% 1.60/0.58    inference(cnf_transformation,[],[f28])).
% 1.60/0.58  fof(f28,plain,(
% 1.60/0.58    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) & r2_hidden(sK1,sK2)),
% 1.60/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f27])).
% 1.60/0.58  fof(f27,plain,(
% 1.60/0.58    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK2 != k2_xboole_0(k1_tarski(sK1),sK2) & r2_hidden(sK1,sK2))),
% 1.60/0.58    introduced(choice_axiom,[])).
% 1.60/0.58  fof(f21,plain,(
% 1.60/0.58    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.60/0.58    inference(ennf_transformation,[],[f20])).
% 1.60/0.58  fof(f20,negated_conjecture,(
% 1.60/0.58    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.60/0.58    inference(negated_conjecture,[],[f19])).
% 1.60/0.58  fof(f19,conjecture,(
% 1.60/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.60/0.58  fof(f544,plain,(
% 1.60/0.58    ~r2_hidden(sK1,sK2)),
% 1.60/0.58    inference(duplicate_literal_removal,[],[f541])).
% 1.60/0.58  fof(f541,plain,(
% 1.60/0.58    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK1,sK2)),
% 1.60/0.58    inference(resolution,[],[f540,f83])).
% 1.60/0.58  fof(f83,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.60/0.58    inference(definition_unfolding,[],[f69,f72])).
% 1.60/0.58  fof(f72,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.60/0.58    inference(definition_unfolding,[],[f47,f71])).
% 1.60/0.58  fof(f71,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.60/0.58    inference(definition_unfolding,[],[f60,f70])).
% 1.60/0.58  fof(f70,plain,(
% 1.60/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f16])).
% 1.60/0.58  fof(f16,axiom,(
% 1.60/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.60/0.58  fof(f60,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f15])).
% 1.60/0.58  fof(f15,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.60/0.58  fof(f47,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f14])).
% 1.60/0.58  fof(f14,axiom,(
% 1.60/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.60/0.58  fof(f69,plain,(
% 1.60/0.58    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f39])).
% 1.60/0.58  fof(f39,plain,(
% 1.60/0.58    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.60/0.58    inference(flattening,[],[f38])).
% 1.60/0.58  fof(f38,plain,(
% 1.60/0.58    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.60/0.58    inference(nnf_transformation,[],[f18])).
% 1.60/0.58  fof(f18,axiom,(
% 1.60/0.58    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.60/0.58  fof(f540,plain,(
% 1.60/0.58    ~r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)),
% 1.60/0.58    inference(trivial_inequality_removal,[],[f537])).
% 1.60/0.58  fof(f537,plain,(
% 1.60/0.58    sK2 != sK2 | ~r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2)),
% 1.60/0.58    inference(superposition,[],[f120,f465])).
% 1.60/0.58  fof(f465,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.60/0.58    inference(forward_demodulation,[],[f464,f76])).
% 1.60/0.58  fof(f76,plain,(
% 1.60/0.58    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.60/0.58    inference(definition_unfolding,[],[f42,f73])).
% 1.60/0.58  fof(f73,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.60/0.58    inference(definition_unfolding,[],[f48,f72])).
% 1.60/0.58  fof(f48,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f17])).
% 1.60/0.58  fof(f17,axiom,(
% 1.60/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.60/0.58  fof(f42,plain,(
% 1.60/0.58    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.60/0.58    inference(cnf_transformation,[],[f5])).
% 1.60/0.58  fof(f5,axiom,(
% 1.60/0.58    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.60/0.58  fof(f464,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) | ~r1_tarski(X0,X1)) )),
% 1.60/0.58    inference(forward_demodulation,[],[f165,f255])).
% 1.60/0.58  fof(f255,plain,(
% 1.60/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.60/0.58    inference(subsumption_resolution,[],[f247,f86])).
% 1.60/0.58  fof(f86,plain,(
% 1.60/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.60/0.58    inference(equality_resolution,[],[f55])).
% 1.60/0.58  fof(f55,plain,(
% 1.60/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.60/0.58    inference(cnf_transformation,[],[f30])).
% 1.60/0.58  fof(f30,plain,(
% 1.60/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.60/0.58    inference(flattening,[],[f29])).
% 1.60/0.58  fof(f29,plain,(
% 1.60/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.60/0.58    inference(nnf_transformation,[],[f3])).
% 1.60/0.58  fof(f3,axiom,(
% 1.60/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.60/0.58  fof(f247,plain,(
% 1.60/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X0)) )),
% 1.60/0.58    inference(superposition,[],[f242,f53])).
% 1.60/0.58  fof(f53,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f22])).
% 1.60/0.58  fof(f22,plain,(
% 1.60/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.60/0.58    inference(ennf_transformation,[],[f7])).
% 1.60/0.58  fof(f7,axiom,(
% 1.60/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.60/0.58  fof(f242,plain,(
% 1.60/0.58    ( ! [X6] : (k1_xboole_0 = k5_xboole_0(X6,k3_xboole_0(X6,X6))) )),
% 1.60/0.58    inference(forward_demodulation,[],[f241,f202])).
% 1.60/0.58  fof(f202,plain,(
% 1.60/0.58    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.60/0.58    inference(superposition,[],[f195,f153])).
% 1.60/0.58  fof(f153,plain,(
% 1.60/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.60/0.58    inference(resolution,[],[f141,f139])).
% 1.60/0.58  fof(f139,plain,(
% 1.60/0.58    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X1,X2),X1)) )),
% 1.60/0.58    inference(superposition,[],[f121,f79])).
% 1.60/0.58  fof(f79,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 1.60/0.58    inference(definition_unfolding,[],[f46,f73])).
% 1.60/0.58  fof(f46,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.60/0.58    inference(cnf_transformation,[],[f6])).
% 1.60/0.58  fof(f6,axiom,(
% 1.60/0.58    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.60/0.58  fof(f121,plain,(
% 1.60/0.58    ( ! [X2,X1] : (r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))) )),
% 1.60/0.58    inference(superposition,[],[f77,f78])).
% 1.60/0.58  fof(f78,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 1.60/0.58    inference(definition_unfolding,[],[f45,f72,f72])).
% 1.60/0.58  fof(f45,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f12])).
% 1.60/0.58  fof(f12,axiom,(
% 1.60/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.60/0.58  fof(f77,plain,(
% 1.60/0.58    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.60/0.58    inference(definition_unfolding,[],[f44,f73])).
% 1.60/0.58  fof(f44,plain,(
% 1.60/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f11])).
% 1.60/0.58  fof(f11,axiom,(
% 1.60/0.58    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.60/0.58  fof(f141,plain,(
% 1.60/0.58    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.60/0.58    inference(resolution,[],[f138,f56])).
% 1.60/0.58  fof(f56,plain,(
% 1.60/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f30])).
% 1.60/0.58  fof(f138,plain,(
% 1.60/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.60/0.58    inference(superposition,[],[f121,f76])).
% 1.60/0.58  fof(f195,plain,(
% 1.60/0.58    ( ! [X1] : (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1) )),
% 1.60/0.58    inference(forward_demodulation,[],[f189,f126])).
% 1.60/0.58  fof(f126,plain,(
% 1.60/0.58    ( ! [X15] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X15)) = X15) )),
% 1.60/0.58    inference(superposition,[],[f76,f78])).
% 1.60/0.58  fof(f189,plain,(
% 1.60/0.58    ( ! [X1] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) )),
% 1.60/0.58    inference(superposition,[],[f126,f81])).
% 1.60/0.58  fof(f81,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.60/0.58    inference(definition_unfolding,[],[f51,f73,f49,f73])).
% 1.60/0.58  fof(f49,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.60/0.58    inference(cnf_transformation,[],[f4])).
% 1.60/0.58  fof(f4,axiom,(
% 1.60/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.60/0.58  fof(f51,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f8])).
% 1.60/0.58  fof(f8,axiom,(
% 1.60/0.58    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.60/0.58  fof(f241,plain,(
% 1.60/0.58    ( ! [X6] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X6,k3_xboole_0(X6,X6))) )),
% 1.60/0.58    inference(forward_demodulation,[],[f230,f153])).
% 1.60/0.58  fof(f230,plain,(
% 1.60/0.58    ( ! [X6] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X6)) = k5_xboole_0(X6,k3_xboole_0(X6,X6))) )),
% 1.60/0.58    inference(superposition,[],[f80,f126])).
% 1.60/0.58  fof(f80,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 1.60/0.58    inference(definition_unfolding,[],[f50,f49,f49,f73])).
% 1.60/0.58  fof(f50,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f9])).
% 1.60/0.58  fof(f9,axiom,(
% 1.60/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.60/0.58  fof(f165,plain,(
% 1.60/0.58    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k5_xboole_0(X0,X0))) | ~r1_tarski(X0,X1)) )),
% 1.60/0.58    inference(superposition,[],[f81,f53])).
% 1.60/0.58  fof(f120,plain,(
% 1.60/0.58    sK2 != k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.60/0.58    inference(backward_demodulation,[],[f75,f78])).
% 1.60/0.58  fof(f75,plain,(
% 1.60/0.58    sK2 != k3_tarski(k3_enumset1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2))),
% 1.60/0.58    inference(definition_unfolding,[],[f41,f73,f74])).
% 1.60/0.58  fof(f74,plain,(
% 1.60/0.58    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.60/0.58    inference(definition_unfolding,[],[f43,f72])).
% 1.60/0.58  fof(f43,plain,(
% 1.60/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f13])).
% 1.60/0.58  fof(f13,axiom,(
% 1.60/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.60/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.60/0.58  fof(f41,plain,(
% 1.60/0.58    sK2 != k2_xboole_0(k1_tarski(sK1),sK2)),
% 1.60/0.58    inference(cnf_transformation,[],[f28])).
% 1.60/0.58  % SZS output end Proof for theBenchmark
% 1.60/0.58  % (19774)------------------------------
% 1.60/0.58  % (19774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (19774)Termination reason: Refutation
% 1.60/0.58  
% 1.60/0.58  % (19774)Memory used [KB]: 6396
% 1.60/0.58  % (19774)Time elapsed: 0.184 s
% 1.60/0.58  % (19774)------------------------------
% 1.60/0.58  % (19774)------------------------------
% 1.60/0.58  % (19746)Success in time 0.219 s
%------------------------------------------------------------------------------
