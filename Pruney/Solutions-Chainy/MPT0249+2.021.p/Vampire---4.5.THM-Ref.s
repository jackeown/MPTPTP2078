%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:13 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 331 expanded)
%              Number of leaves         :   16 (  95 expanded)
%              Depth                    :   19
%              Number of atoms          :  147 ( 797 expanded)
%              Number of equality atoms :   96 ( 701 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f944,plain,(
    $false ),
    inference(subsumption_resolution,[],[f943,f40])).

fof(f40,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f943,plain,(
    k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f249,f942])).

fof(f942,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f938,f41])).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f938,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f403,f935])).

fof(f935,plain,(
    sK1 = k4_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f262,f934])).

fof(f934,plain,(
    sK1 = k5_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f933,f38])).

fof(f38,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f933,plain,
    ( sK1 = sK2
    | sK1 = k5_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f917,f163])).

fof(f163,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f37,f158])).

fof(f158,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f157,f39])).

fof(f39,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f157,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f54,f69])).

fof(f69,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f45,f37])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f37,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f917,plain,
    ( sK1 = k5_xboole_0(sK1,sK2)
    | sK2 = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f439,f262])).

fof(f439,plain,(
    ! [X0] :
      ( sK1 = k4_xboole_0(sK1,X0)
      | k2_xboole_0(sK1,X0) = X0 ) ),
    inference(resolution,[],[f317,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f317,plain,(
    ! [X3] :
      ( r1_tarski(sK1,X3)
      | sK1 = k4_xboole_0(sK1,X3) ) ),
    inference(forward_demodulation,[],[f310,f158])).

fof(f310,plain,(
    ! [X3] :
      ( r1_tarski(sK1,X3)
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),X3) ) ),
    inference(resolution,[],[f305,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(resolution,[],[f53,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f305,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | r1_tarski(sK1,X0) ) ),
    inference(superposition,[],[f300,f158])).

fof(f300,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f299])).

fof(f299,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f61,f42])).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f262,plain,(
    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f49,f249])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f403,plain,(
    ! [X12,X11] : k3_xboole_0(X11,X12) = k5_xboole_0(k4_xboole_0(X11,X12),X11) ),
    inference(superposition,[],[f342,f49])).

fof(f342,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f274,f274])).

fof(f274,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f248,f46])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f248,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f217,f116])).

fof(f116,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f115,f43])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f115,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f105,f44])).

fof(f44,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f105,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f50,f41])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f217,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f58,f41])).

fof(f58,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f249,plain,(
    sK2 = k3_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f201,f248])).

fof(f201,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f160,f46])).

fof(f160,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) ),
    inference(backward_demodulation,[],[f112,f158])).

fof(f112,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0)) ),
    inference(superposition,[],[f50,f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:58:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (3712)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (3728)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (3720)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (3711)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (3710)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (3717)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (3717)Refutation not found, incomplete strategy% (3717)------------------------------
% 0.21/0.53  % (3717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3717)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3717)Memory used [KB]: 10618
% 0.21/0.53  % (3717)Time elapsed: 0.106 s
% 0.21/0.53  % (3717)------------------------------
% 0.21/0.53  % (3717)------------------------------
% 0.21/0.53  % (3729)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (3727)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (3721)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (3721)Refutation not found, incomplete strategy% (3721)------------------------------
% 0.21/0.54  % (3721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3721)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3721)Memory used [KB]: 6140
% 0.21/0.54  % (3721)Time elapsed: 0.002 s
% 0.21/0.54  % (3721)------------------------------
% 0.21/0.54  % (3721)------------------------------
% 0.21/0.54  % (3722)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (3732)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (3719)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (3718)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (3706)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (3708)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (3735)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (3730)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (3709)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (3713)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (3731)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (3724)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (3734)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (3733)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (3714)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (3726)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.28/0.55  % (3716)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.28/0.56  % (3716)Refutation not found, incomplete strategy% (3716)------------------------------
% 1.28/0.56  % (3716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.56  % (3716)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.56  
% 1.28/0.56  % (3716)Memory used [KB]: 10618
% 1.28/0.56  % (3716)Time elapsed: 0.139 s
% 1.28/0.56  % (3716)------------------------------
% 1.28/0.56  % (3716)------------------------------
% 1.28/0.56  % (3725)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.54/0.57  % (3707)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.54/0.59  % (3723)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.54/0.59  % (3723)Refutation not found, incomplete strategy% (3723)------------------------------
% 1.54/0.59  % (3723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.59  % (3723)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.59  
% 1.54/0.59  % (3723)Memory used [KB]: 10618
% 1.54/0.59  % (3723)Time elapsed: 0.151 s
% 1.54/0.59  % (3723)------------------------------
% 1.54/0.59  % (3723)------------------------------
% 1.54/0.59  % (3715)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.54/0.60  % (3713)Refutation found. Thanks to Tanya!
% 1.54/0.60  % SZS status Theorem for theBenchmark
% 1.54/0.60  % SZS output start Proof for theBenchmark
% 1.54/0.62  fof(f944,plain,(
% 1.54/0.62    $false),
% 1.54/0.62    inference(subsumption_resolution,[],[f943,f40])).
% 1.54/0.62  fof(f40,plain,(
% 1.54/0.62    k1_xboole_0 != sK2),
% 1.54/0.62    inference(cnf_transformation,[],[f32])).
% 1.54/0.62  fof(f32,plain,(
% 1.54/0.62    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.54/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f31])).
% 1.54/0.62  fof(f31,plain,(
% 1.54/0.62    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.54/0.62    introduced(choice_axiom,[])).
% 1.54/0.62  fof(f27,plain,(
% 1.54/0.62    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.54/0.62    inference(ennf_transformation,[],[f23])).
% 1.54/0.62  fof(f23,negated_conjecture,(
% 1.54/0.62    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.54/0.62    inference(negated_conjecture,[],[f22])).
% 1.54/0.62  fof(f22,conjecture,(
% 1.54/0.62    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.54/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.54/0.62  fof(f943,plain,(
% 1.54/0.62    k1_xboole_0 = sK2),
% 1.54/0.62    inference(backward_demodulation,[],[f249,f942])).
% 1.54/0.62  fof(f942,plain,(
% 1.54/0.62    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.54/0.62    inference(forward_demodulation,[],[f938,f41])).
% 1.54/0.62  fof(f41,plain,(
% 1.54/0.62    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 1.54/0.62    inference(cnf_transformation,[],[f9])).
% 1.54/0.62  fof(f9,axiom,(
% 1.54/0.62    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 1.54/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.54/0.62  fof(f938,plain,(
% 1.54/0.62    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK1)),
% 1.54/0.62    inference(superposition,[],[f403,f935])).
% 1.54/0.62  fof(f935,plain,(
% 1.54/0.62    sK1 = k4_xboole_0(sK1,sK2)),
% 1.54/0.62    inference(backward_demodulation,[],[f262,f934])).
% 1.54/0.62  fof(f934,plain,(
% 1.54/0.62    sK1 = k5_xboole_0(sK1,sK2)),
% 1.54/0.62    inference(subsumption_resolution,[],[f933,f38])).
% 1.54/0.62  fof(f38,plain,(
% 1.54/0.62    sK1 != sK2),
% 1.54/0.62    inference(cnf_transformation,[],[f32])).
% 1.54/0.62  fof(f933,plain,(
% 1.54/0.62    sK1 = sK2 | sK1 = k5_xboole_0(sK1,sK2)),
% 1.54/0.62    inference(forward_demodulation,[],[f917,f163])).
% 1.54/0.62  fof(f163,plain,(
% 1.54/0.62    sK1 = k2_xboole_0(sK1,sK2)),
% 1.54/0.62    inference(backward_demodulation,[],[f37,f158])).
% 1.54/0.62  fof(f158,plain,(
% 1.54/0.62    sK1 = k1_tarski(sK0)),
% 1.54/0.62    inference(subsumption_resolution,[],[f157,f39])).
% 1.54/0.62  fof(f39,plain,(
% 1.54/0.62    k1_xboole_0 != sK1),
% 1.54/0.62    inference(cnf_transformation,[],[f32])).
% 1.54/0.62  fof(f157,plain,(
% 1.54/0.62    k1_xboole_0 = sK1 | sK1 = k1_tarski(sK0)),
% 1.54/0.62    inference(resolution,[],[f54,f69])).
% 1.54/0.62  fof(f69,plain,(
% 1.54/0.62    r1_tarski(sK1,k1_tarski(sK0))),
% 1.54/0.62    inference(superposition,[],[f45,f37])).
% 1.54/0.62  fof(f45,plain,(
% 1.54/0.62    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.54/0.62    inference(cnf_transformation,[],[f6])).
% 1.54/0.62  fof(f6,axiom,(
% 1.54/0.62    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.54/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.54/0.62  fof(f54,plain,(
% 1.54/0.62    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.54/0.62    inference(cnf_transformation,[],[f34])).
% 1.54/0.62  fof(f34,plain,(
% 1.54/0.62    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.54/0.62    inference(flattening,[],[f33])).
% 1.54/0.62  fof(f33,plain,(
% 1.54/0.62    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.54/0.62    inference(nnf_transformation,[],[f19])).
% 1.54/0.62  fof(f19,axiom,(
% 1.54/0.62    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.54/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.54/0.62  fof(f37,plain,(
% 1.54/0.62    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.54/0.62    inference(cnf_transformation,[],[f32])).
% 1.54/0.62  fof(f917,plain,(
% 1.54/0.62    sK1 = k5_xboole_0(sK1,sK2) | sK2 = k2_xboole_0(sK1,sK2)),
% 1.54/0.62    inference(superposition,[],[f439,f262])).
% 1.54/0.62  fof(f439,plain,(
% 1.54/0.62    ( ! [X0] : (sK1 = k4_xboole_0(sK1,X0) | k2_xboole_0(sK1,X0) = X0) )),
% 1.54/0.62    inference(resolution,[],[f317,f52])).
% 1.54/0.62  fof(f52,plain,(
% 1.54/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.54/0.62    inference(cnf_transformation,[],[f29])).
% 1.54/0.62  fof(f29,plain,(
% 1.54/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.54/0.62    inference(ennf_transformation,[],[f5])).
% 1.54/0.62  fof(f5,axiom,(
% 1.54/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.54/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.54/0.62  fof(f317,plain,(
% 1.54/0.62    ( ! [X3] : (r1_tarski(sK1,X3) | sK1 = k4_xboole_0(sK1,X3)) )),
% 1.54/0.62    inference(forward_demodulation,[],[f310,f158])).
% 1.54/0.62  fof(f310,plain,(
% 1.54/0.62    ( ! [X3] : (r1_tarski(sK1,X3) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),X3)) )),
% 1.54/0.62    inference(resolution,[],[f305,f78])).
% 1.54/0.62  fof(f78,plain,(
% 1.54/0.62    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.54/0.62    inference(resolution,[],[f53,f51])).
% 1.54/0.62  fof(f51,plain,(
% 1.54/0.62    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f28])).
% 1.54/0.62  fof(f28,plain,(
% 1.54/0.62    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.54/0.62    inference(ennf_transformation,[],[f18])).
% 1.54/0.62  fof(f18,axiom,(
% 1.54/0.62    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.54/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.54/0.62  fof(f53,plain,(
% 1.54/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.54/0.62    inference(cnf_transformation,[],[f30])).
% 1.54/0.62  fof(f30,plain,(
% 1.54/0.62    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.54/0.62    inference(ennf_transformation,[],[f26])).
% 1.54/0.62  fof(f26,plain,(
% 1.54/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 1.54/0.62    inference(unused_predicate_definition_removal,[],[f7])).
% 1.54/0.62  fof(f7,axiom,(
% 1.54/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.54/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.54/0.62  fof(f305,plain,(
% 1.54/0.62    ( ! [X0] : (~r2_hidden(sK0,X0) | r1_tarski(sK1,X0)) )),
% 1.54/0.62    inference(superposition,[],[f300,f158])).
% 1.54/0.62  fof(f300,plain,(
% 1.54/0.62    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.54/0.62    inference(duplicate_literal_removal,[],[f299])).
% 1.54/0.62  fof(f299,plain,(
% 1.54/0.62    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.54/0.62    inference(superposition,[],[f61,f42])).
% 1.54/0.62  fof(f42,plain,(
% 1.54/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f11])).
% 1.54/0.62  fof(f11,axiom,(
% 1.54/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.54/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.54/0.62  fof(f61,plain,(
% 1.54/0.62    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f36])).
% 1.54/0.62  fof(f36,plain,(
% 1.54/0.62    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.54/0.62    inference(flattening,[],[f35])).
% 1.54/0.62  fof(f35,plain,(
% 1.54/0.62    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.54/0.62    inference(nnf_transformation,[],[f21])).
% 1.54/0.62  fof(f21,axiom,(
% 1.54/0.62    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.54/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.54/0.62  fof(f262,plain,(
% 1.54/0.62    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK2)),
% 1.54/0.62    inference(superposition,[],[f49,f249])).
% 1.54/0.62  fof(f49,plain,(
% 1.54/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.54/0.62    inference(cnf_transformation,[],[f4])).
% 1.54/0.62  fof(f4,axiom,(
% 1.54/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.54/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.54/0.62  fof(f403,plain,(
% 1.54/0.62    ( ! [X12,X11] : (k3_xboole_0(X11,X12) = k5_xboole_0(k4_xboole_0(X11,X12),X11)) )),
% 1.54/0.62    inference(superposition,[],[f342,f49])).
% 1.54/0.62  fof(f342,plain,(
% 1.54/0.62    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 1.54/0.62    inference(superposition,[],[f274,f274])).
% 1.54/0.62  fof(f274,plain,(
% 1.54/0.62    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 1.54/0.62    inference(superposition,[],[f248,f46])).
% 1.54/0.62  fof(f46,plain,(
% 1.54/0.62    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.54/0.62    inference(cnf_transformation,[],[f1])).
% 1.54/0.62  fof(f1,axiom,(
% 1.54/0.62    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.54/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.54/0.62  fof(f248,plain,(
% 1.54/0.62    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.54/0.62    inference(forward_demodulation,[],[f217,f116])).
% 1.54/0.62  fof(f116,plain,(
% 1.54/0.62    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.54/0.62    inference(forward_demodulation,[],[f115,f43])).
% 1.54/0.62  fof(f43,plain,(
% 1.54/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.54/0.62    inference(cnf_transformation,[],[f24])).
% 1.54/0.62  fof(f24,plain,(
% 1.54/0.62    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.54/0.62    inference(rectify,[],[f3])).
% 1.54/0.62  fof(f3,axiom,(
% 1.54/0.62    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.54/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.54/0.62  fof(f115,plain,(
% 1.54/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.54/0.62    inference(forward_demodulation,[],[f105,f44])).
% 1.54/0.62  fof(f44,plain,(
% 1.54/0.62    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.54/0.62    inference(cnf_transformation,[],[f25])).
% 1.54/0.62  fof(f25,plain,(
% 1.54/0.62    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.54/0.62    inference(rectify,[],[f2])).
% 1.54/0.62  fof(f2,axiom,(
% 1.54/0.62    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.54/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.54/0.62  fof(f105,plain,(
% 1.54/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 1.54/0.62    inference(superposition,[],[f50,f41])).
% 1.54/0.62  fof(f50,plain,(
% 1.54/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.54/0.62    inference(cnf_transformation,[],[f10])).
% 1.54/0.62  fof(f10,axiom,(
% 1.54/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.54/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.54/0.62  fof(f217,plain,(
% 1.54/0.62    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.54/0.62    inference(superposition,[],[f58,f41])).
% 1.54/0.62  fof(f58,plain,(
% 1.54/0.62    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.54/0.62    inference(cnf_transformation,[],[f8])).
% 1.54/0.62  fof(f8,axiom,(
% 1.54/0.62    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.54/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.54/0.62  fof(f249,plain,(
% 1.54/0.62    sK2 = k3_xboole_0(sK1,sK2)),
% 1.54/0.62    inference(backward_demodulation,[],[f201,f248])).
% 1.54/0.62  fof(f201,plain,(
% 1.54/0.62    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),
% 1.54/0.62    inference(superposition,[],[f160,f46])).
% 1.54/0.62  fof(f160,plain,(
% 1.54/0.62    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)),
% 1.54/0.62    inference(backward_demodulation,[],[f112,f158])).
% 1.54/0.62  fof(f112,plain,(
% 1.54/0.62    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0))),
% 1.54/0.62    inference(superposition,[],[f50,f37])).
% 1.54/0.62  % SZS output end Proof for theBenchmark
% 1.54/0.62  % (3713)------------------------------
% 1.54/0.62  % (3713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.62  % (3713)Termination reason: Refutation
% 1.54/0.62  
% 1.54/0.62  % (3713)Memory used [KB]: 6908
% 1.54/0.62  % (3713)Time elapsed: 0.149 s
% 1.54/0.62  % (3713)------------------------------
% 1.54/0.62  % (3713)------------------------------
% 1.54/0.62  % (3705)Success in time 0.25 s
%------------------------------------------------------------------------------
