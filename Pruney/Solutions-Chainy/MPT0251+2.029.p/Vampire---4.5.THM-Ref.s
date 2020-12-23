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
% DateTime   : Thu Dec  3 12:38:38 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 120 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :   16
%              Number of atoms          :  135 ( 234 expanded)
%              Number of equality atoms :   49 ( 106 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f427,plain,(
    $false ),
    inference(subsumption_resolution,[],[f426,f97])).

fof(f97,plain,(
    sK2 != k2_xboole_0(sK2,k1_tarski(sK1)) ),
    inference(superposition,[],[f43,f92])).

fof(f92,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f82,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f82,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f49,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f43,plain,(
    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK2 != k2_xboole_0(k1_tarski(sK1),sK2)
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK2 != k2_xboole_0(k1_tarski(sK1),sK2)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f426,plain,(
    sK2 = k2_xboole_0(sK2,k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f410,f45])).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f410,plain,(
    k2_xboole_0(sK2,k1_tarski(sK1)) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f341,f402])).

fof(f402,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4) ),
    inference(forward_demodulation,[],[f400,f105])).

fof(f105,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f104,f44])).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f104,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f50,f84])).

fof(f84,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f53,f76])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f400,plain,(
    ! [X4] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X4) ),
    inference(superposition,[],[f50,f383])).

fof(f383,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3) ),
    inference(resolution,[],[f380,f53])).

fof(f380,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f376,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f376,plain,(
    ! [X5] : ~ r2_hidden(X5,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f375])).

fof(f375,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_xboole_0)
      | ~ r2_hidden(X5,k1_xboole_0)
      | ~ r2_hidden(X5,k1_xboole_0) ) ),
    inference(superposition,[],[f72,f105])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f341,plain,(
    k2_xboole_0(sK2,k1_tarski(sK1)) = k2_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k1_tarski(sK1))) ),
    inference(superposition,[],[f52,f334])).

fof(f334,plain,(
    k4_xboole_0(k1_tarski(sK1),sK2) = k4_xboole_0(k1_xboole_0,k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f332,f116])).

fof(f116,plain,(
    ! [X1] : k5_xboole_0(X1,X1) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f110,f104])).

fof(f110,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X6,X6) ),
    inference(superposition,[],[f51,f94])).

fof(f94,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f92,f45])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f332,plain,(
    k4_xboole_0(k1_tarski(sK1),sK2) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) ),
    inference(superposition,[],[f50,f327])).

fof(f327,plain,(
    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),sK2) ),
    inference(resolution,[],[f85,f42])).

fof(f42,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f85,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,X2)
      | k1_tarski(X1) = k3_xboole_0(k1_tarski(X1),X2) ) ),
    inference(resolution,[],[f53,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:37:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.55  % (4903)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.23/0.55  % (4900)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.56  % (4895)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.23/0.56  % (4887)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.56  % (4892)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.23/0.56  % (4884)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.58  % (4900)Refutation not found, incomplete strategy% (4900)------------------------------
% 0.23/0.58  % (4900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.58  % (4900)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.58  
% 0.23/0.58  % (4900)Memory used [KB]: 10746
% 0.23/0.58  % (4900)Time elapsed: 0.141 s
% 0.23/0.58  % (4900)------------------------------
% 0.23/0.58  % (4900)------------------------------
% 0.23/0.59  % (4883)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.23/0.59  % (4882)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.23/0.60  % (4902)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.23/0.60  % (4888)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.23/0.60  % (4889)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.23/0.60  % (4889)Refutation not found, incomplete strategy% (4889)------------------------------
% 0.23/0.60  % (4889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.60  % (4889)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.60  
% 0.23/0.60  % (4889)Memory used [KB]: 10618
% 0.23/0.60  % (4889)Time elapsed: 0.166 s
% 0.23/0.60  % (4889)------------------------------
% 0.23/0.60  % (4889)------------------------------
% 0.23/0.60  % (4886)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.23/0.60  % (4907)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.60  % (4896)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.23/0.60  % (4891)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.60  % (4890)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.60  % (4879)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.60  % (4905)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.79/0.61  % (4904)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.79/0.61  % (4881)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.79/0.61  % (4898)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.79/0.61  % (4898)Refutation not found, incomplete strategy% (4898)------------------------------
% 1.79/0.61  % (4898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.61  % (4893)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.79/0.61  % (4897)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.79/0.61  % (4894)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.79/0.61  % (4885)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.79/0.61  % (4878)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.79/0.62  % (4880)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.79/0.62  % (4906)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.79/0.62  % (4888)Refutation not found, incomplete strategy% (4888)------------------------------
% 1.79/0.62  % (4888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.62  % (4888)Termination reason: Refutation not found, incomplete strategy
% 1.79/0.62  
% 1.79/0.62  % (4888)Memory used [KB]: 10618
% 1.79/0.62  % (4888)Time elapsed: 0.140 s
% 1.79/0.62  % (4888)------------------------------
% 1.79/0.62  % (4888)------------------------------
% 1.79/0.62  % (4899)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.96/0.63  % (4898)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.63  
% 1.96/0.63  % (4898)Memory used [KB]: 10746
% 1.96/0.63  % (4898)Time elapsed: 0.174 s
% 1.96/0.63  % (4898)------------------------------
% 1.96/0.63  % (4898)------------------------------
% 1.96/0.63  % (4901)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.96/0.64  % (4885)Refutation found. Thanks to Tanya!
% 1.96/0.64  % SZS status Theorem for theBenchmark
% 1.96/0.65  % SZS output start Proof for theBenchmark
% 1.96/0.65  fof(f427,plain,(
% 1.96/0.65    $false),
% 1.96/0.65    inference(subsumption_resolution,[],[f426,f97])).
% 1.96/0.65  fof(f97,plain,(
% 1.96/0.65    sK2 != k2_xboole_0(sK2,k1_tarski(sK1))),
% 1.96/0.65    inference(superposition,[],[f43,f92])).
% 1.96/0.65  fof(f92,plain,(
% 1.96/0.65    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 1.96/0.65    inference(superposition,[],[f82,f49])).
% 1.96/0.65  fof(f49,plain,(
% 1.96/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.96/0.65    inference(cnf_transformation,[],[f17])).
% 1.96/0.65  fof(f17,axiom,(
% 1.96/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.96/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.96/0.65  fof(f82,plain,(
% 1.96/0.65    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 1.96/0.65    inference(superposition,[],[f49,f47])).
% 1.96/0.65  fof(f47,plain,(
% 1.96/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.96/0.65    inference(cnf_transformation,[],[f11])).
% 1.96/0.65  fof(f11,axiom,(
% 1.96/0.65    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.96/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.96/0.65  fof(f43,plain,(
% 1.96/0.65    sK2 != k2_xboole_0(k1_tarski(sK1),sK2)),
% 1.96/0.65    inference(cnf_transformation,[],[f27])).
% 1.96/0.65  fof(f27,plain,(
% 1.96/0.65    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) & r2_hidden(sK1,sK2)),
% 1.96/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26])).
% 1.96/0.65  fof(f26,plain,(
% 1.96/0.65    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK2 != k2_xboole_0(k1_tarski(sK1),sK2) & r2_hidden(sK1,sK2))),
% 1.96/0.65    introduced(choice_axiom,[])).
% 1.96/0.65  fof(f20,plain,(
% 1.96/0.65    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.96/0.65    inference(ennf_transformation,[],[f19])).
% 1.96/0.65  fof(f19,negated_conjecture,(
% 1.96/0.65    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.96/0.65    inference(negated_conjecture,[],[f18])).
% 1.96/0.65  fof(f18,conjecture,(
% 1.96/0.65    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.96/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.96/0.65  fof(f426,plain,(
% 1.96/0.65    sK2 = k2_xboole_0(sK2,k1_tarski(sK1))),
% 1.96/0.65    inference(forward_demodulation,[],[f410,f45])).
% 1.96/0.65  fof(f45,plain,(
% 1.96/0.65    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.96/0.65    inference(cnf_transformation,[],[f6])).
% 1.96/0.65  fof(f6,axiom,(
% 1.96/0.65    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.96/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.96/0.65  fof(f410,plain,(
% 1.96/0.65    k2_xboole_0(sK2,k1_tarski(sK1)) = k2_xboole_0(sK2,k1_xboole_0)),
% 1.96/0.65    inference(backward_demodulation,[],[f341,f402])).
% 1.96/0.65  fof(f402,plain,(
% 1.96/0.65    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4)) )),
% 1.96/0.65    inference(forward_demodulation,[],[f400,f105])).
% 1.96/0.65  fof(f105,plain,(
% 1.96/0.65    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.96/0.65    inference(superposition,[],[f104,f44])).
% 1.96/0.65  fof(f44,plain,(
% 1.96/0.65    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.96/0.65    inference(cnf_transformation,[],[f9])).
% 1.96/0.65  fof(f9,axiom,(
% 1.96/0.65    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.96/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.96/0.65  fof(f104,plain,(
% 1.96/0.65    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.96/0.65    inference(superposition,[],[f50,f84])).
% 1.96/0.65  fof(f84,plain,(
% 1.96/0.65    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.96/0.65    inference(resolution,[],[f53,f76])).
% 1.96/0.65  fof(f76,plain,(
% 1.96/0.65    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.96/0.65    inference(equality_resolution,[],[f55])).
% 1.96/0.65  fof(f55,plain,(
% 1.96/0.65    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.96/0.65    inference(cnf_transformation,[],[f29])).
% 1.96/0.65  fof(f29,plain,(
% 1.96/0.65    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.96/0.65    inference(flattening,[],[f28])).
% 1.96/0.65  fof(f28,plain,(
% 1.96/0.65    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.96/0.65    inference(nnf_transformation,[],[f4])).
% 1.96/0.65  fof(f4,axiom,(
% 1.96/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.96/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.96/0.65  fof(f53,plain,(
% 1.96/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.96/0.65    inference(cnf_transformation,[],[f21])).
% 1.96/0.65  fof(f21,plain,(
% 1.96/0.65    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.96/0.65    inference(ennf_transformation,[],[f7])).
% 1.96/0.65  fof(f7,axiom,(
% 1.96/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.96/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.96/0.65  fof(f50,plain,(
% 1.96/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.96/0.65    inference(cnf_transformation,[],[f5])).
% 1.96/0.65  fof(f5,axiom,(
% 1.96/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.96/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.96/0.65  fof(f400,plain,(
% 1.96/0.65    ( ! [X4] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X4)) )),
% 1.96/0.65    inference(superposition,[],[f50,f383])).
% 1.96/0.65  fof(f383,plain,(
% 1.96/0.65    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3)) )),
% 1.96/0.65    inference(resolution,[],[f380,f53])).
% 1.96/0.65  fof(f380,plain,(
% 1.96/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.96/0.65    inference(resolution,[],[f376,f58])).
% 1.96/0.65  fof(f58,plain,(
% 1.96/0.65    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.96/0.65    inference(cnf_transformation,[],[f33])).
% 1.96/0.65  fof(f33,plain,(
% 1.96/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.96/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 1.96/0.65  fof(f32,plain,(
% 1.96/0.65    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.96/0.65    introduced(choice_axiom,[])).
% 1.96/0.65  fof(f31,plain,(
% 1.96/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.96/0.65    inference(rectify,[],[f30])).
% 1.96/0.65  fof(f30,plain,(
% 1.96/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.96/0.65    inference(nnf_transformation,[],[f22])).
% 1.96/0.65  fof(f22,plain,(
% 1.96/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.96/0.65    inference(ennf_transformation,[],[f1])).
% 1.96/0.65  fof(f1,axiom,(
% 1.96/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.96/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.96/0.65  fof(f376,plain,(
% 1.96/0.65    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0)) )),
% 1.96/0.65    inference(duplicate_literal_removal,[],[f375])).
% 1.96/0.65  fof(f375,plain,(
% 1.96/0.65    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0) | ~r2_hidden(X5,k1_xboole_0) | ~r2_hidden(X5,k1_xboole_0)) )),
% 1.96/0.65    inference(superposition,[],[f72,f105])).
% 1.96/0.65  fof(f72,plain,(
% 1.96/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.96/0.65    inference(cnf_transformation,[],[f41])).
% 1.96/0.65  fof(f41,plain,(
% 1.96/0.65    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.96/0.65    inference(nnf_transformation,[],[f23])).
% 1.96/0.65  fof(f23,plain,(
% 1.96/0.65    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.96/0.65    inference(ennf_transformation,[],[f3])).
% 1.96/0.65  fof(f3,axiom,(
% 1.96/0.65    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.96/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.96/0.65  fof(f341,plain,(
% 1.96/0.65    k2_xboole_0(sK2,k1_tarski(sK1)) = k2_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k1_tarski(sK1)))),
% 1.96/0.65    inference(superposition,[],[f52,f334])).
% 1.96/0.65  fof(f334,plain,(
% 1.96/0.65    k4_xboole_0(k1_tarski(sK1),sK2) = k4_xboole_0(k1_xboole_0,k1_tarski(sK1))),
% 1.96/0.65    inference(forward_demodulation,[],[f332,f116])).
% 1.96/0.65  fof(f116,plain,(
% 1.96/0.65    ( ! [X1] : (k5_xboole_0(X1,X1) = k4_xboole_0(k1_xboole_0,X1)) )),
% 1.96/0.65    inference(superposition,[],[f110,f104])).
% 1.96/0.65  fof(f110,plain,(
% 1.96/0.65    ( ! [X6] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X6,X6)) )),
% 1.96/0.65    inference(superposition,[],[f51,f94])).
% 1.96/0.65  fof(f94,plain,(
% 1.96/0.65    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.96/0.65    inference(superposition,[],[f92,f45])).
% 1.96/0.65  fof(f51,plain,(
% 1.96/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.96/0.65    inference(cnf_transformation,[],[f10])).
% 1.96/0.65  fof(f10,axiom,(
% 1.96/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.96/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.96/0.65  fof(f332,plain,(
% 1.96/0.65    k4_xboole_0(k1_tarski(sK1),sK2) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1))),
% 1.96/0.65    inference(superposition,[],[f50,f327])).
% 1.96/0.65  fof(f327,plain,(
% 1.96/0.65    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),sK2)),
% 1.96/0.65    inference(resolution,[],[f85,f42])).
% 1.96/0.65  fof(f42,plain,(
% 1.96/0.65    r2_hidden(sK1,sK2)),
% 1.96/0.65    inference(cnf_transformation,[],[f27])).
% 1.96/0.65  fof(f85,plain,(
% 1.96/0.65    ( ! [X2,X1] : (~r2_hidden(X1,X2) | k1_tarski(X1) = k3_xboole_0(k1_tarski(X1),X2)) )),
% 1.96/0.65    inference(resolution,[],[f53,f61])).
% 1.96/0.65  fof(f61,plain,(
% 1.96/0.65    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.96/0.65    inference(cnf_transformation,[],[f34])).
% 1.96/0.65  fof(f34,plain,(
% 1.96/0.65    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.96/0.65    inference(nnf_transformation,[],[f16])).
% 1.96/0.65  fof(f16,axiom,(
% 1.96/0.65    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.96/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.96/0.65  fof(f52,plain,(
% 1.96/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.96/0.65    inference(cnf_transformation,[],[f8])).
% 1.96/0.65  fof(f8,axiom,(
% 1.96/0.65    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.96/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.96/0.65  % SZS output end Proof for theBenchmark
% 1.96/0.65  % (4885)------------------------------
% 1.96/0.65  % (4885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.65  % (4885)Termination reason: Refutation
% 1.96/0.65  
% 1.96/0.65  % (4885)Memory used [KB]: 6524
% 1.96/0.65  % (4885)Time elapsed: 0.209 s
% 1.96/0.65  % (4885)------------------------------
% 1.96/0.65  % (4885)------------------------------
% 1.96/0.65  % (4877)Success in time 0.271 s
%------------------------------------------------------------------------------
