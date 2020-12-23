%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:07 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 125 expanded)
%              Number of leaves         :   12 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  104 ( 210 expanded)
%              Number of equality atoms :   49 ( 116 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f535,plain,(
    $false ),
    inference(subsumption_resolution,[],[f534,f108])).

fof(f108,plain,(
    sK2 != k2_xboole_0(sK2,k2_tarski(sK1,sK3)) ),
    inference(superposition,[],[f45,f101])).

fof(f101,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f81,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f49,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f45,plain,(
    sK2 != k2_xboole_0(k2_tarski(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK2 != k2_xboole_0(k2_tarski(sK1,sK3),sK2)
    & r2_hidden(sK3,sK2)
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( sK2 != k2_xboole_0(k2_tarski(sK1,sK3),sK2)
      & r2_hidden(sK3,sK2)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) != X1
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

fof(f534,plain,(
    sK2 = k2_xboole_0(sK2,k2_tarski(sK1,sK3)) ),
    inference(forward_demodulation,[],[f533,f47])).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f533,plain,(
    k2_xboole_0(sK2,k2_tarski(sK1,sK3)) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f53,f528])).

fof(f528,plain,(
    k1_xboole_0 = k4_xboole_0(k2_tarski(sK1,sK3),sK2) ),
    inference(forward_demodulation,[],[f526,f150])).

fof(f150,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f104,f148])).

fof(f148,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(X5,X5) ),
    inference(backward_demodulation,[],[f118,f139])).

fof(f139,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f137,f103])).

fof(f103,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f51,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f54,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f54,plain,(
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

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f137,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(forward_demodulation,[],[f130,f105])).

fof(f105,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f101,f47])).

fof(f130,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f53,f105])).

fof(f118,plain,(
    ! [X5] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X5,X5) ),
    inference(forward_demodulation,[],[f117,f103])).

fof(f117,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(X5,X5) ),
    inference(superposition,[],[f52,f105])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f104,plain,(
    ! [X1] : k5_xboole_0(X1,X1) = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f51,f84])).

fof(f84,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(resolution,[],[f54,f78])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
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

fof(f526,plain,(
    k4_xboole_0(k2_tarski(sK1,sK3),sK2) = k5_xboole_0(k2_tarski(sK1,sK3),k2_tarski(sK1,sK3)) ),
    inference(superposition,[],[f51,f439])).

fof(f439,plain,(
    k2_tarski(sK1,sK3) = k3_xboole_0(k2_tarski(sK1,sK3),sK2) ),
    inference(resolution,[],[f428,f54])).

fof(f428,plain,(
    r1_tarski(k2_tarski(sK1,sK3),sK2) ),
    inference(resolution,[],[f422,f44])).

fof(f44,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f422,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r1_tarski(k2_tarski(sK1,X0),sK2) ) ),
    inference(resolution,[],[f72,f43])).

fof(f43,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:10:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (29896)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (29905)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (29901)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (29897)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (29910)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.53  % (29895)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.54  % (29912)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.29/0.54  % (29904)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.54  % (29912)Refutation not found, incomplete strategy% (29912)------------------------------
% 1.29/0.54  % (29912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (29914)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.29/0.54  % (29899)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.54  % (29906)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.29/0.54  % (29918)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.54  % (29894)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.55  % (29892)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.55  % (29915)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.55  % (29919)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.29/0.55  % (29893)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.55  % (29900)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.29/0.55  % (29898)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.55  % (29891)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.55  % (29912)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (29912)Memory used [KB]: 1663
% 1.29/0.55  % (29912)Time elapsed: 0.119 s
% 1.29/0.55  % (29912)------------------------------
% 1.29/0.55  % (29912)------------------------------
% 1.29/0.55  % (29903)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.55  % (29901)Refutation not found, incomplete strategy% (29901)------------------------------
% 1.45/0.55  % (29901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (29901)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (29901)Memory used [KB]: 10618
% 1.45/0.55  % (29901)Time elapsed: 0.136 s
% 1.45/0.55  % (29901)------------------------------
% 1.45/0.55  % (29901)------------------------------
% 1.45/0.55  % (29909)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.55  % (29913)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.45/0.55  % (29911)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.45/0.55  % (29917)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.56  % (29908)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.56  % (29916)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.45/0.56  % (29913)Refutation not found, incomplete strategy% (29913)------------------------------
% 1.45/0.56  % (29913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (29913)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (29913)Memory used [KB]: 10746
% 1.45/0.56  % (29913)Time elapsed: 0.139 s
% 1.45/0.56  % (29913)------------------------------
% 1.45/0.56  % (29913)------------------------------
% 1.45/0.56  % (29902)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.56  % (29907)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.56  % (29920)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.45/0.58  % (29911)Refutation not found, incomplete strategy% (29911)------------------------------
% 1.45/0.58  % (29911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.58  % (29911)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.58  
% 1.45/0.58  % (29911)Memory used [KB]: 10746
% 1.45/0.58  % (29911)Time elapsed: 0.144 s
% 1.45/0.58  % (29911)------------------------------
% 1.45/0.58  % (29911)------------------------------
% 1.45/0.60  % (29898)Refutation found. Thanks to Tanya!
% 1.45/0.60  % SZS status Theorem for theBenchmark
% 1.45/0.60  % SZS output start Proof for theBenchmark
% 1.45/0.60  fof(f535,plain,(
% 1.45/0.60    $false),
% 1.45/0.60    inference(subsumption_resolution,[],[f534,f108])).
% 1.45/0.60  fof(f108,plain,(
% 1.45/0.60    sK2 != k2_xboole_0(sK2,k2_tarski(sK1,sK3))),
% 1.45/0.60    inference(superposition,[],[f45,f101])).
% 1.45/0.60  fof(f101,plain,(
% 1.45/0.60    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 1.45/0.60    inference(superposition,[],[f81,f49])).
% 1.45/0.60  fof(f49,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.45/0.60    inference(cnf_transformation,[],[f15])).
% 1.45/0.60  fof(f15,axiom,(
% 1.45/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.45/0.60  fof(f81,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))) )),
% 1.45/0.60    inference(superposition,[],[f49,f48])).
% 1.45/0.60  fof(f48,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f11])).
% 1.45/0.60  fof(f11,axiom,(
% 1.45/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.45/0.60  fof(f45,plain,(
% 1.45/0.60    sK2 != k2_xboole_0(k2_tarski(sK1,sK3),sK2)),
% 1.45/0.60    inference(cnf_transformation,[],[f27])).
% 1.45/0.60  fof(f27,plain,(
% 1.45/0.60    sK2 != k2_xboole_0(k2_tarski(sK1,sK3),sK2) & r2_hidden(sK3,sK2) & r2_hidden(sK1,sK2)),
% 1.45/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f26])).
% 1.45/0.60  fof(f26,plain,(
% 1.45/0.60    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (sK2 != k2_xboole_0(k2_tarski(sK1,sK3),sK2) & r2_hidden(sK3,sK2) & r2_hidden(sK1,sK2))),
% 1.45/0.60    introduced(choice_axiom,[])).
% 1.45/0.60  fof(f20,plain,(
% 1.45/0.60    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 1.45/0.60    inference(flattening,[],[f19])).
% 1.45/0.60  fof(f19,plain,(
% 1.45/0.60    ? [X0,X1,X2] : (k2_xboole_0(k2_tarski(X0,X2),X1) != X1 & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 1.45/0.60    inference(ennf_transformation,[],[f18])).
% 1.45/0.60  fof(f18,negated_conjecture,(
% 1.45/0.60    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 1.45/0.60    inference(negated_conjecture,[],[f17])).
% 1.45/0.60  fof(f17,conjecture,(
% 1.45/0.60    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_xboole_0(k2_tarski(X0,X2),X1) = X1)),
% 1.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).
% 1.45/0.60  fof(f534,plain,(
% 1.45/0.60    sK2 = k2_xboole_0(sK2,k2_tarski(sK1,sK3))),
% 1.45/0.60    inference(forward_demodulation,[],[f533,f47])).
% 1.45/0.60  fof(f47,plain,(
% 1.45/0.60    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.45/0.60    inference(cnf_transformation,[],[f6])).
% 1.45/0.60  fof(f6,axiom,(
% 1.45/0.60    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.45/0.60  fof(f533,plain,(
% 1.45/0.60    k2_xboole_0(sK2,k2_tarski(sK1,sK3)) = k2_xboole_0(sK2,k1_xboole_0)),
% 1.45/0.60    inference(superposition,[],[f53,f528])).
% 1.45/0.60  fof(f528,plain,(
% 1.45/0.60    k1_xboole_0 = k4_xboole_0(k2_tarski(sK1,sK3),sK2)),
% 1.45/0.60    inference(forward_demodulation,[],[f526,f150])).
% 1.45/0.60  fof(f150,plain,(
% 1.45/0.60    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 1.45/0.60    inference(backward_demodulation,[],[f104,f148])).
% 1.45/0.60  fof(f148,plain,(
% 1.45/0.60    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(X5,X5)) )),
% 1.45/0.60    inference(backward_demodulation,[],[f118,f139])).
% 1.45/0.60  fof(f139,plain,(
% 1.45/0.60    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.45/0.60    inference(superposition,[],[f137,f103])).
% 1.45/0.60  fof(f103,plain,(
% 1.45/0.60    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.45/0.60    inference(superposition,[],[f51,f83])).
% 1.45/0.60  fof(f83,plain,(
% 1.45/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.45/0.60    inference(resolution,[],[f54,f46])).
% 1.45/0.60  fof(f46,plain,(
% 1.45/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f8])).
% 1.45/0.60  fof(f8,axiom,(
% 1.45/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.45/0.60  fof(f54,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.45/0.60    inference(cnf_transformation,[],[f21])).
% 1.45/0.60  fof(f21,plain,(
% 1.45/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.45/0.60    inference(ennf_transformation,[],[f7])).
% 1.45/0.60  fof(f7,axiom,(
% 1.45/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.45/0.60  fof(f51,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.45/0.60    inference(cnf_transformation,[],[f5])).
% 1.45/0.60  fof(f5,axiom,(
% 1.45/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.45/0.60  fof(f137,plain,(
% 1.45/0.60    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6) )),
% 1.45/0.60    inference(forward_demodulation,[],[f130,f105])).
% 1.45/0.60  fof(f105,plain,(
% 1.45/0.60    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.45/0.60    inference(superposition,[],[f101,f47])).
% 1.45/0.60  fof(f130,plain,(
% 1.45/0.60    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6)) )),
% 1.45/0.60    inference(superposition,[],[f53,f105])).
% 1.45/0.60  fof(f118,plain,(
% 1.45/0.60    ( ! [X5] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X5,X5)) )),
% 1.45/0.60    inference(forward_demodulation,[],[f117,f103])).
% 1.45/0.60  fof(f117,plain,(
% 1.45/0.60    ( ! [X5] : (k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(X5,X5)) )),
% 1.45/0.60    inference(superposition,[],[f52,f105])).
% 1.45/0.60  fof(f52,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f10])).
% 1.45/0.60  fof(f10,axiom,(
% 1.45/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.45/0.60  fof(f104,plain,(
% 1.45/0.60    ( ! [X1] : (k5_xboole_0(X1,X1) = k4_xboole_0(X1,X1)) )),
% 1.45/0.60    inference(superposition,[],[f51,f84])).
% 1.45/0.60  fof(f84,plain,(
% 1.45/0.60    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 1.45/0.60    inference(resolution,[],[f54,f78])).
% 1.45/0.60  fof(f78,plain,(
% 1.45/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.45/0.60    inference(equality_resolution,[],[f56])).
% 1.45/0.60  fof(f56,plain,(
% 1.45/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.45/0.60    inference(cnf_transformation,[],[f29])).
% 1.45/0.60  fof(f29,plain,(
% 1.45/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.45/0.60    inference(flattening,[],[f28])).
% 1.45/0.60  fof(f28,plain,(
% 1.45/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.45/0.60    inference(nnf_transformation,[],[f4])).
% 1.45/0.60  fof(f4,axiom,(
% 1.45/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.45/0.60  fof(f526,plain,(
% 1.45/0.60    k4_xboole_0(k2_tarski(sK1,sK3),sK2) = k5_xboole_0(k2_tarski(sK1,sK3),k2_tarski(sK1,sK3))),
% 1.45/0.60    inference(superposition,[],[f51,f439])).
% 1.45/0.60  fof(f439,plain,(
% 1.45/0.60    k2_tarski(sK1,sK3) = k3_xboole_0(k2_tarski(sK1,sK3),sK2)),
% 1.45/0.60    inference(resolution,[],[f428,f54])).
% 1.45/0.60  fof(f428,plain,(
% 1.45/0.60    r1_tarski(k2_tarski(sK1,sK3),sK2)),
% 1.45/0.60    inference(resolution,[],[f422,f44])).
% 1.45/0.60  fof(f44,plain,(
% 1.45/0.60    r2_hidden(sK3,sK2)),
% 1.45/0.60    inference(cnf_transformation,[],[f27])).
% 1.45/0.60  fof(f422,plain,(
% 1.45/0.60    ( ! [X0] : (~r2_hidden(X0,sK2) | r1_tarski(k2_tarski(sK1,X0),sK2)) )),
% 1.45/0.60    inference(resolution,[],[f72,f43])).
% 1.45/0.60  fof(f43,plain,(
% 1.45/0.60    r2_hidden(sK1,sK2)),
% 1.45/0.60    inference(cnf_transformation,[],[f27])).
% 1.45/0.60  fof(f72,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f41])).
% 1.45/0.60  fof(f41,plain,(
% 1.45/0.60    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.45/0.60    inference(flattening,[],[f40])).
% 1.45/0.60  fof(f40,plain,(
% 1.45/0.60    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.45/0.60    inference(nnf_transformation,[],[f16])).
% 1.45/0.60  fof(f16,axiom,(
% 1.45/0.60    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.45/0.60  fof(f53,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f9])).
% 1.45/0.60  fof(f9,axiom,(
% 1.45/0.60    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.45/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.45/0.60  % SZS output end Proof for theBenchmark
% 1.45/0.60  % (29898)------------------------------
% 1.45/0.60  % (29898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.60  % (29898)Termination reason: Refutation
% 1.45/0.60  
% 1.45/0.60  % (29898)Memory used [KB]: 6524
% 1.45/0.60  % (29898)Time elapsed: 0.152 s
% 1.45/0.60  % (29898)------------------------------
% 1.45/0.60  % (29898)------------------------------
% 1.45/0.60  % (29890)Success in time 0.227 s
%------------------------------------------------------------------------------
