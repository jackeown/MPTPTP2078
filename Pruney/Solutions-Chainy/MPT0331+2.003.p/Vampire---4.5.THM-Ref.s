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
% DateTime   : Thu Dec  3 12:43:05 EST 2020

% Result     : Theorem 3.50s
% Output     : Refutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 241 expanded)
%              Number of leaves         :   16 (  60 expanded)
%              Depth                    :   21
%              Number of atoms          :  143 ( 555 expanded)
%              Number of equality atoms :   81 ( 397 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3945,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3889,f52])).

fof(f52,plain,(
    sK2 != k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f30,plain,(
    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f3889,plain,(
    sK2 = k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f3123,f533])).

fof(f533,plain,(
    k2_enumset1(sK0,sK0,sK0,sK1) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    inference(resolution,[],[f352,f28])).

fof(f28,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f352,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | k2_enumset1(X1,X1,X1,sK1) = k4_xboole_0(k2_enumset1(X1,X1,X1,sK1),sK2) ) ),
    inference(resolution,[],[f55,f29])).

fof(f29,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | k2_enumset1(X0,X0,X0,X1) = k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f51,f37,f37])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f3123,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X18,X17)) = X17 ),
    inference(forward_demodulation,[],[f3033,f253])).

fof(f253,plain,(
    ! [X5] : k4_xboole_0(X5,k1_xboole_0) = X5 ),
    inference(forward_demodulation,[],[f239,f235])).

fof(f235,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(resolution,[],[f212,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f212,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f204,f31])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f204,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | ~ r1_tarski(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)) ) ),
    inference(superposition,[],[f48,f198])).

fof(f198,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f197,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f197,plain,(
    ! [X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f184,f60])).

fof(f184,plain,(
    ! [X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(superposition,[],[f46,f60])).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f239,plain,(
    ! [X5] : k4_xboole_0(X5,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X5) ),
    inference(superposition,[],[f235,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f3033,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X18,X17)) = k4_xboole_0(X17,k1_xboole_0) ),
    inference(superposition,[],[f53,f785])).

fof(f785,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f615,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f45,f33,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f615,plain,(
    ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X6,X7),X6) ),
    inference(forward_demodulation,[],[f602,f452])).

fof(f452,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(X3,X3) ),
    inference(backward_demodulation,[],[f244,f445])).

fof(f445,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4) ),
    inference(resolution,[],[f429,f234])).

fof(f234,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f212,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f429,plain,(
    ! [X6,X7] : r1_tarski(k4_xboole_0(k1_xboole_0,X6),X7) ),
    inference(subsumption_resolution,[],[f403,f31])).

fof(f403,plain,(
    ! [X6,X7] :
      ( r1_tarski(k4_xboole_0(k1_xboole_0,X6),X7)
      | ~ r1_tarski(X6,k2_xboole_0(X6,X7)) ) ),
    inference(superposition,[],[f48,f244])).

fof(f244,plain,(
    ! [X3] : k4_xboole_0(X3,X3) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f36,f235])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f602,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X6) = k4_xboole_0(k4_xboole_0(X6,X7),X6) ),
    inference(superposition,[],[f36,f560])).

fof(f560,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2 ),
    inference(resolution,[],[f111,f62])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f31,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

% (12453)Time limit reached!
% (12453)------------------------------
% (12453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12453)Termination reason: Time limit

% (12453)Memory used [KB]: 14072
% (12453)Time elapsed: 0.500 s
% (12453)------------------------------
% (12453)------------------------------
fof(f111,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,k2_xboole_0(X4,X5))
      | k2_xboole_0(k4_xboole_0(X3,X4),X5) = X5 ) ),
    inference(resolution,[],[f48,f38])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f33])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:10:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (12448)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (12476)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (12476)Refutation not found, incomplete strategy% (12476)------------------------------
% 0.22/0.52  % (12476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12476)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12476)Memory used [KB]: 1663
% 0.22/0.52  % (12476)Time elapsed: 0.004 s
% 0.22/0.52  % (12476)------------------------------
% 0.22/0.52  % (12476)------------------------------
% 0.22/0.52  % (12460)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (12452)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (12448)Refutation not found, incomplete strategy% (12448)------------------------------
% 0.22/0.52  % (12448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12448)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12448)Memory used [KB]: 1663
% 0.22/0.52  % (12448)Time elapsed: 0.112 s
% 0.22/0.52  % (12448)------------------------------
% 0.22/0.52  % (12448)------------------------------
% 0.22/0.53  % (12465)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (12449)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (12457)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (12457)Refutation not found, incomplete strategy% (12457)------------------------------
% 0.22/0.53  % (12457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12447)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (12457)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12457)Memory used [KB]: 10746
% 0.22/0.54  % (12457)Time elapsed: 0.122 s
% 0.22/0.54  % (12457)------------------------------
% 0.22/0.54  % (12457)------------------------------
% 0.22/0.54  % (12466)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (12451)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.40/0.54  % (12472)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.40/0.55  % (12455)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.40/0.55  % (12464)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.40/0.55  % (12459)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.40/0.55  % (12458)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.40/0.56  % (12471)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.40/0.56  % (12456)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.40/0.56  % (12450)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.55/0.56  % (12467)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.55/0.56  % (12461)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.55/0.57  % (12475)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.55/0.57  % (12475)Refutation not found, incomplete strategy% (12475)------------------------------
% 1.55/0.57  % (12475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (12475)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (12475)Memory used [KB]: 10746
% 1.55/0.57  % (12475)Time elapsed: 0.159 s
% 1.55/0.57  % (12475)------------------------------
% 1.55/0.57  % (12475)------------------------------
% 1.55/0.57  % (12453)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.57  % (12474)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.55/0.57  % (12459)Refutation not found, incomplete strategy% (12459)------------------------------
% 1.55/0.57  % (12459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (12459)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (12459)Memory used [KB]: 10618
% 1.55/0.57  % (12459)Time elapsed: 0.161 s
% 1.55/0.57  % (12459)------------------------------
% 1.55/0.57  % (12459)------------------------------
% 1.55/0.57  % (12469)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.55/0.57  % (12463)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.55/0.57  % (12454)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.55/0.58  % (12463)Refutation not found, incomplete strategy% (12463)------------------------------
% 1.55/0.58  % (12463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (12463)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (12463)Memory used [KB]: 10618
% 1.55/0.58  % (12463)Time elapsed: 0.162 s
% 1.55/0.58  % (12463)------------------------------
% 1.55/0.58  % (12463)------------------------------
% 1.55/0.58  % (12473)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.55/0.58  % (12473)Refutation not found, incomplete strategy% (12473)------------------------------
% 1.55/0.58  % (12473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (12473)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (12473)Memory used [KB]: 6268
% 1.55/0.58  % (12473)Time elapsed: 0.167 s
% 1.55/0.58  % (12473)------------------------------
% 1.55/0.58  % (12473)------------------------------
% 1.55/0.58  % (12468)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.55/0.59  % (12462)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.55/0.62  % (12470)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.55/0.62  % (12478)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.00/0.63  % (12477)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.00/0.66  % (12479)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.00/0.66  % (12479)Refutation not found, incomplete strategy% (12479)------------------------------
% 2.00/0.66  % (12479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.66  % (12479)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.66  
% 2.00/0.66  % (12479)Memory used [KB]: 6140
% 2.00/0.66  % (12479)Time elapsed: 0.064 s
% 2.00/0.66  % (12479)------------------------------
% 2.00/0.66  % (12479)------------------------------
% 2.29/0.70  % (12480)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.29/0.70  % (12447)Refutation not found, incomplete strategy% (12447)------------------------------
% 2.29/0.70  % (12447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.29/0.70  % (12447)Termination reason: Refutation not found, incomplete strategy
% 2.29/0.70  
% 2.29/0.70  % (12447)Memory used [KB]: 1663
% 2.29/0.70  % (12447)Time elapsed: 0.268 s
% 2.29/0.70  % (12447)------------------------------
% 2.29/0.70  % (12447)------------------------------
% 2.29/0.73  % (12481)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.75/0.73  % (12482)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.75/0.74  % (12450)Refutation not found, incomplete strategy% (12450)------------------------------
% 2.75/0.74  % (12450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.75/0.74  % (12450)Termination reason: Refutation not found, incomplete strategy
% 2.75/0.74  
% 2.75/0.74  % (12450)Memory used [KB]: 6140
% 2.75/0.74  % (12450)Time elapsed: 0.309 s
% 2.75/0.74  % (12450)------------------------------
% 2.75/0.74  % (12450)------------------------------
% 2.75/0.74  % (12483)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.94/0.80  % (12484)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.94/0.81  % (12449)Time limit reached!
% 2.94/0.81  % (12449)------------------------------
% 2.94/0.81  % (12449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.94/0.83  % (12449)Termination reason: Time limit
% 2.94/0.83  % (12449)Termination phase: Saturation
% 2.94/0.83  
% 2.94/0.83  % (12449)Memory used [KB]: 7547
% 2.94/0.83  % (12449)Time elapsed: 0.400 s
% 2.94/0.83  % (12449)------------------------------
% 2.94/0.83  % (12449)------------------------------
% 3.32/0.83  % (12471)Time limit reached!
% 3.32/0.83  % (12471)------------------------------
% 3.32/0.83  % (12471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.32/0.83  % (12471)Termination reason: Time limit
% 3.32/0.83  % (12471)Termination phase: Saturation
% 3.32/0.83  
% 3.32/0.83  % (12471)Memory used [KB]: 13048
% 3.32/0.83  % (12471)Time elapsed: 0.400 s
% 3.32/0.83  % (12471)------------------------------
% 3.32/0.83  % (12471)------------------------------
% 3.32/0.84  % (12485)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 3.50/0.87  % (12462)Refutation not found, incomplete strategy% (12462)------------------------------
% 3.50/0.87  % (12462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.50/0.87  % (12462)Termination reason: Refutation not found, incomplete strategy
% 3.50/0.87  
% 3.50/0.87  % (12462)Memory used [KB]: 6268
% 3.50/0.87  % (12462)Time elapsed: 0.429 s
% 3.50/0.87  % (12462)------------------------------
% 3.50/0.87  % (12462)------------------------------
% 3.50/0.89  % (12486)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.50/0.89  % (12469)Refutation found. Thanks to Tanya!
% 3.50/0.89  % SZS status Theorem for theBenchmark
% 3.50/0.89  % SZS output start Proof for theBenchmark
% 3.50/0.89  fof(f3945,plain,(
% 3.50/0.89    $false),
% 3.50/0.89    inference(subsumption_resolution,[],[f3889,f52])).
% 3.50/0.89  fof(f52,plain,(
% 3.50/0.89    sK2 != k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 3.50/0.89    inference(definition_unfolding,[],[f30,f37])).
% 3.50/0.89  fof(f37,plain,(
% 3.50/0.89    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.50/0.89    inference(cnf_transformation,[],[f11])).
% 3.50/0.89  fof(f11,axiom,(
% 3.50/0.89    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 3.50/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 3.50/0.89  fof(f30,plain,(
% 3.50/0.89    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 3.50/0.89    inference(cnf_transformation,[],[f21])).
% 3.50/0.89  fof(f21,plain,(
% 3.50/0.89    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 3.50/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f20])).
% 3.50/0.89  fof(f20,plain,(
% 3.50/0.89    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 3.50/0.89    introduced(choice_axiom,[])).
% 3.50/0.89  fof(f17,plain,(
% 3.50/0.89    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 3.50/0.89    inference(ennf_transformation,[],[f16])).
% 3.50/0.89  fof(f16,negated_conjecture,(
% 3.50/0.89    ~! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 3.50/0.89    inference(negated_conjecture,[],[f15])).
% 3.50/0.89  fof(f15,conjecture,(
% 3.50/0.89    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 3.50/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 3.50/0.89  fof(f3889,plain,(
% 3.50/0.89    sK2 = k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 3.50/0.89    inference(superposition,[],[f3123,f533])).
% 3.50/0.89  fof(f533,plain,(
% 3.50/0.89    k2_enumset1(sK0,sK0,sK0,sK1) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 3.50/0.89    inference(resolution,[],[f352,f28])).
% 3.50/0.89  fof(f28,plain,(
% 3.50/0.89    ~r2_hidden(sK0,sK2)),
% 3.50/0.89    inference(cnf_transformation,[],[f21])).
% 3.50/0.89  fof(f352,plain,(
% 3.50/0.89    ( ! [X1] : (r2_hidden(X1,sK2) | k2_enumset1(X1,X1,X1,sK1) = k4_xboole_0(k2_enumset1(X1,X1,X1,sK1),sK2)) )),
% 3.50/0.89    inference(resolution,[],[f55,f29])).
% 3.50/0.89  fof(f29,plain,(
% 3.50/0.89    ~r2_hidden(sK1,sK2)),
% 3.50/0.89    inference(cnf_transformation,[],[f21])).
% 3.50/0.89  fof(f55,plain,(
% 3.50/0.89    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | k2_enumset1(X0,X0,X0,X1) = k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 3.50/0.89    inference(definition_unfolding,[],[f51,f37,f37])).
% 3.50/0.89  fof(f51,plain,(
% 3.50/0.89    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 3.50/0.89    inference(cnf_transformation,[],[f27])).
% 3.50/0.89  fof(f27,plain,(
% 3.50/0.89    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.50/0.89    inference(flattening,[],[f26])).
% 3.50/0.89  fof(f26,plain,(
% 3.50/0.89    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.50/0.89    inference(nnf_transformation,[],[f14])).
% 3.50/0.89  fof(f14,axiom,(
% 3.50/0.89    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.50/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 3.50/0.89  fof(f3123,plain,(
% 3.50/0.89    ( ! [X17,X18] : (k4_xboole_0(X17,k4_xboole_0(X18,X17)) = X17) )),
% 3.50/0.89    inference(forward_demodulation,[],[f3033,f253])).
% 3.50/0.89  fof(f253,plain,(
% 3.50/0.89    ( ! [X5] : (k4_xboole_0(X5,k1_xboole_0) = X5) )),
% 3.50/0.89    inference(forward_demodulation,[],[f239,f235])).
% 3.50/0.89  fof(f235,plain,(
% 3.50/0.89    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 3.50/0.89    inference(resolution,[],[f212,f38])).
% 3.50/0.89  fof(f38,plain,(
% 3.50/0.89    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 3.50/0.89    inference(cnf_transformation,[],[f18])).
% 3.50/0.89  fof(f18,plain,(
% 3.50/0.89    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.50/0.89    inference(ennf_transformation,[],[f3])).
% 3.50/0.89  fof(f3,axiom,(
% 3.50/0.89    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.50/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.50/0.89  fof(f212,plain,(
% 3.50/0.89    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.50/0.89    inference(subsumption_resolution,[],[f204,f31])).
% 3.50/0.89  fof(f31,plain,(
% 3.50/0.89    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.50/0.89    inference(cnf_transformation,[],[f10])).
% 3.50/0.89  fof(f10,axiom,(
% 3.50/0.89    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.50/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.50/0.89  fof(f204,plain,(
% 3.50/0.89    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | ~r1_tarski(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0))) )),
% 3.50/0.89    inference(superposition,[],[f48,f198])).
% 3.50/0.89  fof(f198,plain,(
% 3.50/0.89    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.50/0.89    inference(forward_demodulation,[],[f197,f60])).
% 3.50/0.89  fof(f60,plain,(
% 3.50/0.89    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.50/0.89    inference(equality_resolution,[],[f44])).
% 3.50/0.89  fof(f44,plain,(
% 3.50/0.89    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.50/0.89    inference(cnf_transformation,[],[f25])).
% 3.50/0.89  fof(f25,plain,(
% 3.50/0.89    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.50/0.89    inference(flattening,[],[f24])).
% 3.50/0.89  fof(f24,plain,(
% 3.50/0.89    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.50/0.89    inference(nnf_transformation,[],[f12])).
% 3.50/0.89  fof(f12,axiom,(
% 3.50/0.89    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.50/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 3.50/0.89  fof(f197,plain,(
% 3.50/0.89    ( ! [X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 3.50/0.89    inference(forward_demodulation,[],[f184,f60])).
% 3.50/0.89  fof(f184,plain,(
% 3.50/0.89    ( ! [X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(X1,k1_xboole_0))) )),
% 3.50/0.89    inference(superposition,[],[f46,f60])).
% 3.50/0.89  fof(f46,plain,(
% 3.50/0.89    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 3.50/0.89    inference(cnf_transformation,[],[f13])).
% 3.50/0.89  fof(f13,axiom,(
% 3.50/0.89    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 3.50/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 3.50/0.89  fof(f48,plain,(
% 3.50/0.89    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.50/0.89    inference(cnf_transformation,[],[f19])).
% 3.50/0.89  fof(f19,plain,(
% 3.50/0.89    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.50/0.89    inference(ennf_transformation,[],[f6])).
% 3.50/0.89  fof(f6,axiom,(
% 3.50/0.89    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.50/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 3.50/0.89  fof(f239,plain,(
% 3.50/0.89    ( ! [X5] : (k4_xboole_0(X5,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X5)) )),
% 3.50/0.89    inference(superposition,[],[f235,f34])).
% 3.50/0.89  fof(f34,plain,(
% 3.50/0.89    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.50/0.89    inference(cnf_transformation,[],[f4])).
% 3.50/0.89  fof(f4,axiom,(
% 3.50/0.89    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.50/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 3.50/0.89  fof(f3033,plain,(
% 3.50/0.89    ( ! [X17,X18] : (k4_xboole_0(X17,k4_xboole_0(X18,X17)) = k4_xboole_0(X17,k1_xboole_0)) )),
% 3.50/0.89    inference(superposition,[],[f53,f785])).
% 3.50/0.89  fof(f785,plain,(
% 3.50/0.89    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 3.50/0.89    inference(superposition,[],[f615,f54])).
% 3.50/0.89  fof(f54,plain,(
% 3.50/0.89    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 3.50/0.89    inference(definition_unfolding,[],[f45,f33,f33])).
% 3.50/0.89  fof(f33,plain,(
% 3.50/0.89    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.50/0.89    inference(cnf_transformation,[],[f8])).
% 3.50/0.89  fof(f8,axiom,(
% 3.50/0.89    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.50/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.50/0.89  fof(f45,plain,(
% 3.50/0.89    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.50/0.89    inference(cnf_transformation,[],[f9])).
% 3.50/0.89  fof(f9,axiom,(
% 3.50/0.89    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.50/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 3.50/0.89  fof(f615,plain,(
% 3.50/0.89    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X6,X7),X6)) )),
% 3.50/0.89    inference(forward_demodulation,[],[f602,f452])).
% 3.50/0.89  fof(f452,plain,(
% 3.50/0.89    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3)) )),
% 3.50/0.89    inference(backward_demodulation,[],[f244,f445])).
% 3.50/0.89  fof(f445,plain,(
% 3.50/0.89    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4)) )),
% 3.50/0.89    inference(resolution,[],[f429,f234])).
% 3.50/0.89  fof(f234,plain,(
% 3.50/0.89    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 3.50/0.89    inference(resolution,[],[f212,f41])).
% 3.50/0.89  fof(f41,plain,(
% 3.50/0.89    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.50/0.89    inference(cnf_transformation,[],[f23])).
% 3.50/0.89  fof(f23,plain,(
% 3.50/0.89    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.50/0.89    inference(flattening,[],[f22])).
% 3.50/0.89  fof(f22,plain,(
% 3.50/0.89    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.50/0.89    inference(nnf_transformation,[],[f2])).
% 3.50/0.89  fof(f2,axiom,(
% 3.50/0.89    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.50/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.50/0.89  fof(f429,plain,(
% 3.50/0.89    ( ! [X6,X7] : (r1_tarski(k4_xboole_0(k1_xboole_0,X6),X7)) )),
% 3.50/0.89    inference(subsumption_resolution,[],[f403,f31])).
% 3.50/0.89  fof(f403,plain,(
% 3.50/0.89    ( ! [X6,X7] : (r1_tarski(k4_xboole_0(k1_xboole_0,X6),X7) | ~r1_tarski(X6,k2_xboole_0(X6,X7))) )),
% 3.50/0.89    inference(superposition,[],[f48,f244])).
% 3.50/0.89  fof(f244,plain,(
% 3.50/0.89    ( ! [X3] : (k4_xboole_0(X3,X3) = k4_xboole_0(k1_xboole_0,X3)) )),
% 3.50/0.89    inference(superposition,[],[f36,f235])).
% 3.50/0.89  fof(f36,plain,(
% 3.50/0.89    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 3.50/0.89    inference(cnf_transformation,[],[f5])).
% 3.50/0.89  fof(f5,axiom,(
% 3.50/0.89    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 3.50/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 3.50/0.89  fof(f602,plain,(
% 3.50/0.89    ( ! [X6,X7] : (k4_xboole_0(X6,X6) = k4_xboole_0(k4_xboole_0(X6,X7),X6)) )),
% 3.50/0.89    inference(superposition,[],[f36,f560])).
% 3.50/0.89  fof(f560,plain,(
% 3.50/0.89    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) )),
% 3.50/0.89    inference(resolution,[],[f111,f62])).
% 3.50/0.89  fof(f62,plain,(
% 3.50/0.89    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 3.50/0.89    inference(superposition,[],[f31,f32])).
% 3.50/0.89  fof(f32,plain,(
% 3.50/0.89    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.50/0.89    inference(cnf_transformation,[],[f1])).
% 3.50/0.89  fof(f1,axiom,(
% 3.50/0.89    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.50/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.50/0.91  % (12453)Time limit reached!
% 3.50/0.91  % (12453)------------------------------
% 3.50/0.91  % (12453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.50/0.91  % (12453)Termination reason: Time limit
% 3.50/0.91  
% 3.50/0.91  % (12453)Memory used [KB]: 14072
% 3.50/0.91  % (12453)Time elapsed: 0.500 s
% 3.50/0.91  % (12453)------------------------------
% 3.50/0.91  % (12453)------------------------------
% 3.50/0.91  fof(f111,plain,(
% 3.50/0.91    ( ! [X4,X5,X3] : (~r1_tarski(X3,k2_xboole_0(X4,X5)) | k2_xboole_0(k4_xboole_0(X3,X4),X5) = X5) )),
% 3.50/0.91    inference(resolution,[],[f48,f38])).
% 3.50/0.91  fof(f53,plain,(
% 3.50/0.91    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.50/0.91    inference(definition_unfolding,[],[f35,f33])).
% 3.50/0.91  fof(f35,plain,(
% 3.50/0.91    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.50/0.91    inference(cnf_transformation,[],[f7])).
% 3.50/0.91  fof(f7,axiom,(
% 3.50/0.91    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.50/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 3.50/0.91  % SZS output end Proof for theBenchmark
% 3.50/0.91  % (12469)------------------------------
% 3.50/0.91  % (12469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.50/0.91  % (12469)Termination reason: Refutation
% 3.50/0.91  
% 3.50/0.91  % (12469)Memory used [KB]: 8955
% 3.50/0.91  % (12469)Time elapsed: 0.483 s
% 3.50/0.91  % (12469)------------------------------
% 3.50/0.91  % (12469)------------------------------
% 3.50/0.91  % (12446)Success in time 0.535 s
%------------------------------------------------------------------------------
