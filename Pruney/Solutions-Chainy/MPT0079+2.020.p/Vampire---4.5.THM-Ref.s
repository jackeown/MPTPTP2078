%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:54 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 183 expanded)
%              Number of leaves         :   16 (  56 expanded)
%              Depth                    :   23
%              Number of atoms          :  133 ( 394 expanded)
%              Number of equality atoms :   58 ( 183 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1114,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1113,f60])).

fof(f60,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f40,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1113,plain,(
    ~ r1_tarski(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1112,f33])).

fof(f33,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f1112,plain,(
    ~ r1_tarski(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(forward_demodulation,[],[f1110,f42])).

fof(f1110,plain,(
    ~ r1_tarski(sK1,k2_xboole_0(sK3,sK2)) ),
    inference(resolution,[],[f1104,f892])).

fof(f892,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | ~ r1_tarski(sK1,k2_xboole_0(sK3,X0)) ) ),
    inference(superposition,[],[f53,f827])).

fof(f827,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f801,f37])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f801,plain,(
    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f55,f616])).

fof(f616,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f54,f313])).

fof(f313,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f287,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f287,plain,(
    ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) ),
    inference(resolution,[],[f56,f35])).

fof(f35,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f48,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f41,f43,f43])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f44,f43])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f1104,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f1103,f36])).

fof(f36,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f1103,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK1,sK2) ),
    inference(forward_demodulation,[],[f1097,f37])).

fof(f1097,plain,
    ( sK2 = k4_xboole_0(sK1,k1_xboole_0)
    | ~ r1_tarski(sK1,sK2) ),
    inference(superposition,[],[f1093,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f1093,plain,(
    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f1088,f37])).

fof(f1088,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f54,f1070])).

fof(f1070,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f1062,f819])).

fof(f819,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f791,f37])).

fof(f791,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f55,f616])).

fof(f1062,plain,(
    k4_xboole_0(sK1,sK1) = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f45,f1038])).

fof(f1038,plain,(
    sK1 = k2_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f898,f58])).

fof(f58,plain,(
    r1_tarski(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f40,f33])).

fof(f898,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,k2_xboole_0(sK0,X0))
      | k2_xboole_0(sK2,X0) = X0 ) ),
    inference(resolution,[],[f846,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f846,plain,(
    ! [X0] :
      ( r1_tarski(sK2,X0)
      | ~ r1_tarski(sK2,k2_xboole_0(sK0,X0)) ) ),
    inference(superposition,[],[f53,f828])).

fof(f828,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f802,f37])).

fof(f802,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f55,f288])).

fof(f288,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f286,f38])).

fof(f286,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))) ),
    inference(resolution,[],[f56,f34])).

fof(f34,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:33:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (22410)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (22420)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (22401)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (22402)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (22404)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (22403)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (22400)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (22412)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (22425)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (22413)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (22424)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (22414)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (22421)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (22405)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (22422)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (22415)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (22415)Refutation not found, incomplete strategy% (22415)------------------------------
% 0.22/0.55  % (22415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (22415)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (22415)Memory used [KB]: 6140
% 0.22/0.55  % (22415)Time elapsed: 0.002 s
% 0.22/0.55  % (22415)------------------------------
% 0.22/0.55  % (22415)------------------------------
% 0.22/0.55  % (22406)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (22428)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (22427)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (22419)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (22411)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (22418)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (22423)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (22429)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.56  % (22407)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (22408)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.57  % (22416)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.60/0.59  % (22409)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.60/0.59  % (22403)Refutation found. Thanks to Tanya!
% 1.60/0.59  % SZS status Theorem for theBenchmark
% 1.60/0.59  % SZS output start Proof for theBenchmark
% 1.60/0.59  fof(f1114,plain,(
% 1.60/0.59    $false),
% 1.60/0.59    inference(subsumption_resolution,[],[f1113,f60])).
% 1.60/0.59  fof(f60,plain,(
% 1.60/0.59    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 1.60/0.59    inference(superposition,[],[f40,f42])).
% 1.60/0.59  fof(f42,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f1])).
% 1.60/0.59  fof(f1,axiom,(
% 1.60/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.60/0.59  fof(f40,plain,(
% 1.60/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f15])).
% 1.60/0.59  fof(f15,axiom,(
% 1.60/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.60/0.59  fof(f1113,plain,(
% 1.60/0.59    ~r1_tarski(sK1,k2_xboole_0(sK0,sK1))),
% 1.60/0.59    inference(forward_demodulation,[],[f1112,f33])).
% 1.60/0.59  fof(f33,plain,(
% 1.60/0.59    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.60/0.59    inference(cnf_transformation,[],[f27])).
% 1.60/0.59  fof(f27,plain,(
% 1.60/0.59    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.60/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f26])).
% 1.60/0.59  fof(f26,plain,(
% 1.60/0.59    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 1.60/0.59    introduced(choice_axiom,[])).
% 1.60/0.59  fof(f21,plain,(
% 1.60/0.59    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.60/0.59    inference(flattening,[],[f20])).
% 1.60/0.59  fof(f20,plain,(
% 1.60/0.59    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.60/0.59    inference(ennf_transformation,[],[f17])).
% 1.60/0.59  fof(f17,negated_conjecture,(
% 1.60/0.59    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.60/0.59    inference(negated_conjecture,[],[f16])).
% 1.60/0.59  fof(f16,conjecture,(
% 1.60/0.59    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.60/0.59  fof(f1112,plain,(
% 1.60/0.59    ~r1_tarski(sK1,k2_xboole_0(sK2,sK3))),
% 1.60/0.59    inference(forward_demodulation,[],[f1110,f42])).
% 1.60/0.59  fof(f1110,plain,(
% 1.60/0.59    ~r1_tarski(sK1,k2_xboole_0(sK3,sK2))),
% 1.60/0.59    inference(resolution,[],[f1104,f892])).
% 1.60/0.59  fof(f892,plain,(
% 1.60/0.59    ( ! [X0] : (r1_tarski(sK1,X0) | ~r1_tarski(sK1,k2_xboole_0(sK3,X0))) )),
% 1.60/0.59    inference(superposition,[],[f53,f827])).
% 1.60/0.59  fof(f827,plain,(
% 1.60/0.59    sK1 = k4_xboole_0(sK1,sK3)),
% 1.60/0.59    inference(forward_demodulation,[],[f801,f37])).
% 1.60/0.59  fof(f37,plain,(
% 1.60/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.60/0.59    inference(cnf_transformation,[],[f9])).
% 1.60/0.59  fof(f9,axiom,(
% 1.60/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.60/0.59  fof(f801,plain,(
% 1.60/0.59    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0)),
% 1.60/0.59    inference(superposition,[],[f55,f616])).
% 1.60/0.59  fof(f616,plain,(
% 1.60/0.59    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.60/0.59    inference(superposition,[],[f54,f313])).
% 1.60/0.59  fof(f313,plain,(
% 1.60/0.59    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 1.60/0.59    inference(resolution,[],[f287,f38])).
% 1.60/0.59  fof(f38,plain,(
% 1.60/0.59    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 1.60/0.59    inference(cnf_transformation,[],[f29])).
% 1.60/0.59  fof(f29,plain,(
% 1.60/0.59    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 1.60/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f28])).
% 1.60/0.59  fof(f28,plain,(
% 1.60/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.60/0.59    introduced(choice_axiom,[])).
% 1.60/0.59  fof(f22,plain,(
% 1.60/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.60/0.59    inference(ennf_transformation,[],[f5])).
% 1.60/0.59  fof(f5,axiom,(
% 1.60/0.59    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.60/0.59  fof(f287,plain,(
% 1.60/0.59    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)))) )),
% 1.60/0.59    inference(resolution,[],[f56,f35])).
% 1.60/0.59  fof(f35,plain,(
% 1.60/0.59    r1_xboole_0(sK3,sK1)),
% 1.60/0.59    inference(cnf_transformation,[],[f27])).
% 1.60/0.59  fof(f56,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.60/0.59    inference(definition_unfolding,[],[f48,f43])).
% 1.60/0.59  fof(f43,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f13])).
% 1.60/0.59  fof(f13,axiom,(
% 1.60/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.60/0.59  fof(f48,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f31])).
% 1.60/0.59  fof(f31,plain,(
% 1.60/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.60/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f30])).
% 1.60/0.59  fof(f30,plain,(
% 1.60/0.59    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 1.60/0.59    introduced(choice_axiom,[])).
% 1.60/0.59  fof(f23,plain,(
% 1.60/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.60/0.59    inference(ennf_transformation,[],[f19])).
% 1.60/0.59  fof(f19,plain,(
% 1.60/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.60/0.59    inference(rectify,[],[f4])).
% 1.60/0.59  fof(f4,axiom,(
% 1.60/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.60/0.59  fof(f54,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.60/0.59    inference(definition_unfolding,[],[f41,f43,f43])).
% 1.60/0.59  fof(f41,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f2])).
% 1.60/0.59  fof(f2,axiom,(
% 1.60/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.60/0.59  fof(f55,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.60/0.59    inference(definition_unfolding,[],[f44,f43])).
% 1.60/0.59  fof(f44,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f12])).
% 1.60/0.59  fof(f12,axiom,(
% 1.60/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.60/0.59  fof(f53,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f25])).
% 1.60/0.59  fof(f25,plain,(
% 1.60/0.59    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.60/0.59    inference(ennf_transformation,[],[f11])).
% 1.60/0.59  fof(f11,axiom,(
% 1.60/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.60/0.59  fof(f1104,plain,(
% 1.60/0.59    ~r1_tarski(sK1,sK2)),
% 1.60/0.59    inference(subsumption_resolution,[],[f1103,f36])).
% 1.60/0.59  fof(f36,plain,(
% 1.60/0.59    sK1 != sK2),
% 1.60/0.59    inference(cnf_transformation,[],[f27])).
% 1.60/0.59  fof(f1103,plain,(
% 1.60/0.59    sK1 = sK2 | ~r1_tarski(sK1,sK2)),
% 1.60/0.59    inference(forward_demodulation,[],[f1097,f37])).
% 1.60/0.59  fof(f1097,plain,(
% 1.60/0.59    sK2 = k4_xboole_0(sK1,k1_xboole_0) | ~r1_tarski(sK1,sK2)),
% 1.60/0.59    inference(superposition,[],[f1093,f51])).
% 1.60/0.59  fof(f51,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f32])).
% 1.60/0.59  fof(f32,plain,(
% 1.60/0.59    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.60/0.59    inference(nnf_transformation,[],[f6])).
% 1.60/0.59  fof(f6,axiom,(
% 1.60/0.59    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.60/0.59  fof(f1093,plain,(
% 1.60/0.59    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.60/0.59    inference(forward_demodulation,[],[f1088,f37])).
% 1.60/0.59  fof(f1088,plain,(
% 1.60/0.59    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.60/0.59    inference(superposition,[],[f54,f1070])).
% 1.60/0.59  fof(f1070,plain,(
% 1.60/0.59    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 1.60/0.59    inference(forward_demodulation,[],[f1062,f819])).
% 1.60/0.59  fof(f819,plain,(
% 1.60/0.59    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 1.60/0.59    inference(forward_demodulation,[],[f791,f37])).
% 1.60/0.59  fof(f791,plain,(
% 1.60/0.59    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0))),
% 1.60/0.59    inference(superposition,[],[f55,f616])).
% 1.60/0.59  fof(f1062,plain,(
% 1.60/0.59    k4_xboole_0(sK1,sK1) = k4_xboole_0(sK2,sK1)),
% 1.60/0.59    inference(superposition,[],[f45,f1038])).
% 1.60/0.59  fof(f1038,plain,(
% 1.60/0.59    sK1 = k2_xboole_0(sK2,sK1)),
% 1.60/0.59    inference(resolution,[],[f898,f58])).
% 1.60/0.59  fof(f58,plain,(
% 1.60/0.59    r1_tarski(sK2,k2_xboole_0(sK0,sK1))),
% 1.60/0.59    inference(superposition,[],[f40,f33])).
% 1.60/0.59  fof(f898,plain,(
% 1.60/0.59    ( ! [X0] : (~r1_tarski(sK2,k2_xboole_0(sK0,X0)) | k2_xboole_0(sK2,X0) = X0) )),
% 1.60/0.59    inference(resolution,[],[f846,f49])).
% 1.60/0.59  fof(f49,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.60/0.59    inference(cnf_transformation,[],[f24])).
% 1.60/0.59  fof(f24,plain,(
% 1.60/0.59    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.60/0.59    inference(ennf_transformation,[],[f7])).
% 1.60/0.59  fof(f7,axiom,(
% 1.60/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.60/0.59  fof(f846,plain,(
% 1.60/0.59    ( ! [X0] : (r1_tarski(sK2,X0) | ~r1_tarski(sK2,k2_xboole_0(sK0,X0))) )),
% 1.60/0.59    inference(superposition,[],[f53,f828])).
% 1.60/0.59  fof(f828,plain,(
% 1.60/0.59    sK2 = k4_xboole_0(sK2,sK0)),
% 1.60/0.59    inference(forward_demodulation,[],[f802,f37])).
% 1.60/0.59  fof(f802,plain,(
% 1.60/0.59    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0)),
% 1.60/0.59    inference(superposition,[],[f55,f288])).
% 1.60/0.59  fof(f288,plain,(
% 1.60/0.59    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.60/0.59    inference(resolution,[],[f286,f38])).
% 1.60/0.59  fof(f286,plain,(
% 1.60/0.59    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)))) )),
% 1.60/0.59    inference(resolution,[],[f56,f34])).
% 1.60/0.59  fof(f34,plain,(
% 1.60/0.59    r1_xboole_0(sK2,sK0)),
% 1.60/0.59    inference(cnf_transformation,[],[f27])).
% 1.60/0.59  fof(f45,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f10])).
% 1.60/0.59  fof(f10,axiom,(
% 1.60/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.60/0.59  % SZS output end Proof for theBenchmark
% 1.60/0.59  % (22403)------------------------------
% 1.60/0.59  % (22403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.59  % (22403)Termination reason: Refutation
% 1.60/0.59  
% 1.60/0.59  % (22403)Memory used [KB]: 11257
% 1.60/0.59  % (22403)Time elapsed: 0.164 s
% 1.60/0.59  % (22403)------------------------------
% 1.60/0.59  % (22403)------------------------------
% 1.80/0.60  % (22391)Success in time 0.236 s
%------------------------------------------------------------------------------
