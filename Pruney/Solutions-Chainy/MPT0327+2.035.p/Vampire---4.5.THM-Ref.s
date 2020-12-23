%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 295 expanded)
%              Number of leaves         :   14 (  87 expanded)
%              Depth                    :   16
%              Number of atoms          :  110 ( 470 expanded)
%              Number of equality atoms :   68 ( 258 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f552,plain,(
    $false ),
    inference(subsumption_resolution,[],[f551,f33])).

fof(f33,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f551,plain,(
    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f550,f506])).

fof(f506,plain,(
    sK1 = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f505,f220])).

fof(f220,plain,(
    sK1 = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f219,f172])).

fof(f172,plain,(
    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f92,f166])).

% (27893)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
fof(f166,plain,(
    ! [X5] : k4_xboole_0(X5,k1_xboole_0) = X5 ),
    inference(forward_demodulation,[],[f159,f35])).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f159,plain,(
    ! [X5] : k4_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0) ),
    inference(superposition,[],[f72,f66])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f43,f34])).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f40,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f92,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f77,f91])).

fof(f91,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f86,f40])).

fof(f86,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f42,f35])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f77,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f41,f71])).

fof(f71,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f50,f63])).

fof(f63,plain,(
    r1_tarski(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f48,f32])).

fof(f32,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

% (27911)Refutation not found, incomplete strategy% (27911)------------------------------
% (27911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27911)Termination reason: Refutation not found, incomplete strategy

% (27911)Memory used [KB]: 10746
% (27911)Time elapsed: 0.189 s
% (27911)------------------------------
% (27911)------------------------------
fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f219,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f204,f160])).

fof(f160,plain,(
    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f72,f68])).

fof(f68,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f43,f63])).

fof(f204,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(superposition,[],[f89,f68])).

fof(f89,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f42,f37])).

fof(f505,plain,(
    k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f504,f186])).

fof(f186,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = k5_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) ),
    inference(superposition,[],[f107,f82])).

fof(f82,plain,(
    ! [X0,X1] : k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))) ),
    inference(resolution,[],[f52,f61])).

fof(f61,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f107,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f98,f72])).

fof(f98,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f54,f42])).

fof(f54,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f504,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f503,f149])).

fof(f149,plain,(
    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f68,f37])).

fof(f503,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(sK1,k1_tarski(sK0))) = k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k1_tarski(sK0)),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f471,f160])).

fof(f471,plain,(
    k2_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(sK1,k1_tarski(sK0))) = k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k1_tarski(sK0)),k5_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(superposition,[],[f93,f172])).

fof(f93,plain,(
    ! [X4,X3] : k2_xboole_0(k5_xboole_0(X3,X4),k3_xboole_0(X3,X4)) = k5_xboole_0(k2_xboole_0(X3,X4),k3_xboole_0(k3_xboole_0(X3,X4),k5_xboole_0(X3,X4))) ),
    inference(forward_demodulation,[],[f88,f37])).

fof(f88,plain,(
    ! [X4,X3] : k2_xboole_0(k5_xboole_0(X3,X4),k3_xboole_0(X3,X4)) = k5_xboole_0(k2_xboole_0(X3,X4),k3_xboole_0(k5_xboole_0(X3,X4),k3_xboole_0(X3,X4))) ),
    inference(superposition,[],[f42,f42])).

fof(f550,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f549,f172])).

% (27908)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (27912)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f549,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f541,f160])).

fof(f541,plain,(
    k2_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(superposition,[],[f93,f149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.57  % (27905)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.57  % (27883)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.57  % (27886)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.57  % (27898)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.57  % (27906)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.58  % (27907)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.58  % (27890)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.58  % (27897)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.59  % (27899)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.59  % (27891)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.60  % (27888)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.60  % (27885)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.60  % (27884)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.60  % (27887)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.60  % (27907)Refutation not found, incomplete strategy% (27907)------------------------------
% 0.20/0.60  % (27907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (27907)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.60  
% 0.20/0.60  % (27907)Memory used [KB]: 10618
% 0.20/0.60  % (27907)Time elapsed: 0.159 s
% 0.20/0.60  % (27907)------------------------------
% 0.20/0.60  % (27907)------------------------------
% 0.20/0.60  % (27899)Refutation not found, incomplete strategy% (27899)------------------------------
% 0.20/0.60  % (27899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.61  % (27910)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.61  % (27899)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.61  
% 0.20/0.61  % (27899)Memory used [KB]: 10618
% 0.20/0.61  % (27899)Time elapsed: 0.177 s
% 0.20/0.61  % (27899)------------------------------
% 0.20/0.61  % (27899)------------------------------
% 0.20/0.61  % (27910)Refutation not found, incomplete strategy% (27910)------------------------------
% 0.20/0.61  % (27910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.61  % (27910)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.61  
% 0.20/0.61  % (27910)Memory used [KB]: 6140
% 0.20/0.61  % (27910)Time elapsed: 0.181 s
% 0.20/0.61  % (27910)------------------------------
% 0.20/0.61  % (27910)------------------------------
% 0.20/0.61  % (27903)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.61  % (27902)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.61  % (27889)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.62  % (27894)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.62  % (27895)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.62  % (27890)Refutation found. Thanks to Tanya!
% 0.20/0.62  % SZS status Theorem for theBenchmark
% 0.20/0.62  % (27911)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.62  % (27892)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.62  % SZS output start Proof for theBenchmark
% 0.20/0.62  fof(f552,plain,(
% 0.20/0.62    $false),
% 0.20/0.62    inference(subsumption_resolution,[],[f551,f33])).
% 0.20/0.62  fof(f33,plain,(
% 0.20/0.62    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.20/0.62    inference(cnf_transformation,[],[f24])).
% 0.20/0.62  fof(f24,plain,(
% 0.20/0.62    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 0.20/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).
% 0.20/0.62  fof(f23,plain,(
% 0.20/0.62    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 0.20/0.62    introduced(choice_axiom,[])).
% 0.20/0.62  fof(f21,plain,(
% 0.20/0.62    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 0.20/0.62    inference(ennf_transformation,[],[f20])).
% 0.20/0.62  fof(f20,negated_conjecture,(
% 0.20/0.62    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.20/0.62    inference(negated_conjecture,[],[f19])).
% 0.20/0.62  fof(f19,conjecture,(
% 0.20/0.62    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.20/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 0.20/0.62  fof(f551,plain,(
% 0.20/0.62    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.20/0.62    inference(forward_demodulation,[],[f550,f506])).
% 0.20/0.62  fof(f506,plain,(
% 0.20/0.62    sK1 = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 0.20/0.62    inference(forward_demodulation,[],[f505,f220])).
% 0.20/0.62  fof(f220,plain,(
% 0.20/0.62    sK1 = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.20/0.62    inference(forward_demodulation,[],[f219,f172])).
% 0.20/0.62  fof(f172,plain,(
% 0.20/0.62    sK1 = k2_xboole_0(sK1,k1_tarski(sK0))),
% 0.20/0.62    inference(backward_demodulation,[],[f92,f166])).
% 0.20/0.62  % (27893)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.62  fof(f166,plain,(
% 0.20/0.62    ( ! [X5] : (k4_xboole_0(X5,k1_xboole_0) = X5) )),
% 0.20/0.62    inference(forward_demodulation,[],[f159,f35])).
% 0.20/0.62  fof(f35,plain,(
% 0.20/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.62    inference(cnf_transformation,[],[f8])).
% 0.20/0.62  fof(f8,axiom,(
% 0.20/0.62    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.62  fof(f159,plain,(
% 0.20/0.62    ( ! [X5] : (k4_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0)) )),
% 0.20/0.62    inference(superposition,[],[f72,f66])).
% 0.20/0.62  fof(f66,plain,(
% 0.20/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.62    inference(resolution,[],[f43,f34])).
% 0.20/0.62  fof(f34,plain,(
% 0.20/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.62    inference(cnf_transformation,[],[f6])).
% 0.20/0.62  fof(f6,axiom,(
% 0.20/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.62  fof(f43,plain,(
% 0.20/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.62    inference(cnf_transformation,[],[f22])).
% 0.20/0.62  fof(f22,plain,(
% 0.20/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.62    inference(ennf_transformation,[],[f5])).
% 0.20/0.62  fof(f5,axiom,(
% 0.20/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.62  fof(f72,plain,(
% 0.20/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 0.20/0.62    inference(superposition,[],[f40,f37])).
% 0.20/0.62  fof(f37,plain,(
% 0.20/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.62    inference(cnf_transformation,[],[f1])).
% 0.20/0.62  fof(f1,axiom,(
% 0.20/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.62  fof(f40,plain,(
% 0.20/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.62    inference(cnf_transformation,[],[f4])).
% 0.20/0.62  fof(f4,axiom,(
% 0.20/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.62  fof(f92,plain,(
% 0.20/0.62    k2_xboole_0(sK1,k1_tarski(sK0)) = k4_xboole_0(sK1,k1_xboole_0)),
% 0.20/0.62    inference(backward_demodulation,[],[f77,f91])).
% 0.20/0.62  fof(f91,plain,(
% 0.20/0.62    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.62    inference(forward_demodulation,[],[f86,f40])).
% 0.20/0.62  fof(f86,plain,(
% 0.20/0.62    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.62    inference(superposition,[],[f42,f35])).
% 0.20/0.62  fof(f42,plain,(
% 0.20/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.20/0.62    inference(cnf_transformation,[],[f10])).
% 0.20/0.62  fof(f10,axiom,(
% 0.20/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.20/0.62  fof(f77,plain,(
% 0.20/0.62    k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_xboole_0)),
% 0.20/0.62    inference(superposition,[],[f41,f71])).
% 0.20/0.62  fof(f71,plain,(
% 0.20/0.62    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.62    inference(resolution,[],[f50,f63])).
% 0.20/0.62  fof(f63,plain,(
% 0.20/0.62    r1_tarski(k1_tarski(sK0),sK1)),
% 0.20/0.62    inference(resolution,[],[f48,f32])).
% 0.20/0.62  fof(f32,plain,(
% 0.20/0.62    r2_hidden(sK0,sK1)),
% 0.20/0.62    inference(cnf_transformation,[],[f24])).
% 0.20/0.62  fof(f48,plain,(
% 0.20/0.62    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.20/0.62    inference(cnf_transformation,[],[f27])).
% 0.20/0.62  fof(f27,plain,(
% 0.20/0.62    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.20/0.62    inference(nnf_transformation,[],[f15])).
% 0.20/0.62  fof(f15,axiom,(
% 0.20/0.62    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.62  fof(f50,plain,(
% 0.20/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.62    inference(cnf_transformation,[],[f28])).
% 0.20/0.62  fof(f28,plain,(
% 0.20/0.62    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.62    inference(nnf_transformation,[],[f3])).
% 0.20/0.62  fof(f3,axiom,(
% 0.20/0.62    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.62  fof(f41,plain,(
% 0.20/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.62    inference(cnf_transformation,[],[f7])).
% 0.20/0.62  % (27911)Refutation not found, incomplete strategy% (27911)------------------------------
% 0.20/0.62  % (27911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.62  % (27911)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.62  
% 0.20/0.62  % (27911)Memory used [KB]: 10746
% 0.20/0.62  % (27911)Time elapsed: 0.189 s
% 0.20/0.62  % (27911)------------------------------
% 0.20/0.62  % (27911)------------------------------
% 0.20/0.62  fof(f7,axiom,(
% 0.20/0.62    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.20/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.62  fof(f219,plain,(
% 0.20/0.62    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.20/0.62    inference(forward_demodulation,[],[f204,f160])).
% 0.20/0.62  fof(f160,plain,(
% 0.20/0.62    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0))),
% 0.20/0.62    inference(superposition,[],[f72,f68])).
% 0.20/0.62  fof(f68,plain,(
% 0.20/0.62    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.62    inference(resolution,[],[f43,f63])).
% 0.20/0.62  fof(f204,plain,(
% 0.20/0.62    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.20/0.62    inference(superposition,[],[f89,f68])).
% 0.20/0.62  fof(f89,plain,(
% 0.20/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0))) )),
% 0.20/0.62    inference(superposition,[],[f42,f37])).
% 0.20/0.62  fof(f505,plain,(
% 0.20/0.62    k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 0.20/0.62    inference(forward_demodulation,[],[f504,f186])).
% 0.20/0.62  fof(f186,plain,(
% 0.20/0.62    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = k5_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0))) )),
% 0.20/0.62    inference(superposition,[],[f107,f82])).
% 0.20/0.62  fof(f82,plain,(
% 0.20/0.62    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0)))) )),
% 0.20/0.62    inference(resolution,[],[f52,f61])).
% 0.20/0.62  fof(f61,plain,(
% 0.20/0.62    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.20/0.62    inference(equality_resolution,[],[f56])).
% 0.20/0.62  fof(f56,plain,(
% 0.20/0.62    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.20/0.62    inference(cnf_transformation,[],[f31])).
% 0.20/0.62  fof(f31,plain,(
% 0.20/0.62    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.20/0.62    inference(flattening,[],[f30])).
% 0.20/0.62  fof(f30,plain,(
% 0.20/0.62    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.20/0.62    inference(nnf_transformation,[],[f18])).
% 0.20/0.62  fof(f18,axiom,(
% 0.20/0.62    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.20/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.20/0.62  fof(f52,plain,(
% 0.20/0.62    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.62    inference(cnf_transformation,[],[f29])).
% 0.20/0.62  fof(f29,plain,(
% 0.20/0.62    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.20/0.62    inference(nnf_transformation,[],[f16])).
% 0.20/0.62  fof(f16,axiom,(
% 0.20/0.62    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.20/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.20/0.62  fof(f107,plain,(
% 0.20/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.62    inference(forward_demodulation,[],[f98,f72])).
% 0.20/0.62  fof(f98,plain,(
% 0.20/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 0.20/0.62    inference(superposition,[],[f54,f42])).
% 0.20/0.62  fof(f54,plain,(
% 0.20/0.62    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.62    inference(cnf_transformation,[],[f9])).
% 0.20/0.62  fof(f9,axiom,(
% 0.20/0.62    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.62  fof(f504,plain,(
% 0.20/0.62    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 0.20/0.62    inference(forward_demodulation,[],[f503,f149])).
% 0.20/0.62  fof(f149,plain,(
% 0.20/0.62    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 0.20/0.62    inference(superposition,[],[f68,f37])).
% 0.20/0.62  fof(f503,plain,(
% 0.20/0.62    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(sK1,k1_tarski(sK0))) = k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k1_tarski(sK0)),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 0.20/0.62    inference(forward_demodulation,[],[f471,f160])).
% 0.20/0.62  fof(f471,plain,(
% 0.20/0.62    k2_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(sK1,k1_tarski(sK0))) = k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK1,k1_tarski(sK0)),k5_xboole_0(sK1,k1_tarski(sK0))))),
% 0.20/0.62    inference(superposition,[],[f93,f172])).
% 0.20/0.62  fof(f93,plain,(
% 0.20/0.62    ( ! [X4,X3] : (k2_xboole_0(k5_xboole_0(X3,X4),k3_xboole_0(X3,X4)) = k5_xboole_0(k2_xboole_0(X3,X4),k3_xboole_0(k3_xboole_0(X3,X4),k5_xboole_0(X3,X4)))) )),
% 0.20/0.62    inference(forward_demodulation,[],[f88,f37])).
% 0.20/0.62  fof(f88,plain,(
% 0.20/0.62    ( ! [X4,X3] : (k2_xboole_0(k5_xboole_0(X3,X4),k3_xboole_0(X3,X4)) = k5_xboole_0(k2_xboole_0(X3,X4),k3_xboole_0(k5_xboole_0(X3,X4),k3_xboole_0(X3,X4)))) )),
% 0.20/0.62    inference(superposition,[],[f42,f42])).
% 0.20/0.62  fof(f550,plain,(
% 0.20/0.62    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 0.20/0.62    inference(forward_demodulation,[],[f549,f172])).
% 0.20/0.63  % (27908)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.63  % (27912)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.63  fof(f549,plain,(
% 0.20/0.63    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 0.20/0.63    inference(forward_demodulation,[],[f541,f160])).
% 0.20/0.63  fof(f541,plain,(
% 0.20/0.63    k2_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0))))),
% 0.20/0.63    inference(superposition,[],[f93,f149])).
% 0.20/0.63  % SZS output end Proof for theBenchmark
% 0.20/0.63  % (27890)------------------------------
% 0.20/0.63  % (27890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.63  % (27890)Termination reason: Refutation
% 0.20/0.63  
% 0.20/0.63  % (27890)Memory used [KB]: 2302
% 0.20/0.63  % (27890)Time elapsed: 0.115 s
% 0.20/0.63  % (27890)------------------------------
% 0.20/0.63  % (27890)------------------------------
% 0.20/0.63  % (27909)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.63  % (27912)Refutation not found, incomplete strategy% (27912)------------------------------
% 0.20/0.63  % (27912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.63  % (27912)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.63  
% 0.20/0.63  % (27912)Memory used [KB]: 1663
% 0.20/0.63  % (27912)Time elapsed: 0.195 s
% 0.20/0.63  % (27912)------------------------------
% 0.20/0.63  % (27912)------------------------------
% 0.20/0.63  % (27882)Success in time 0.266 s
%------------------------------------------------------------------------------
