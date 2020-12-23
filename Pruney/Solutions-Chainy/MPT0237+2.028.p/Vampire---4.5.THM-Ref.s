%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:33 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   63 (  89 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 ( 139 expanded)
%              Number of equality atoms :   86 ( 113 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3619,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3618,f40])).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f3618,plain,(
    k1_tarski(sK0) != k2_tarski(sK0,sK0) ),
    inference(forward_demodulation,[],[f3616,f452])).

fof(f452,plain,(
    ! [X14] : k1_tarski(X14) = k2_xboole_0(k1_tarski(X14),k1_tarski(X14)) ),
    inference(forward_demodulation,[],[f437,f135])).

fof(f135,plain,(
    ! [X4] : k5_xboole_0(X4,k1_xboole_0) = X4 ),
    inference(forward_demodulation,[],[f131,f39])).

fof(f39,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f131,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f46,f84])).

fof(f84,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f77,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f50,f38])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f437,plain,(
    ! [X14] : k2_xboole_0(k1_tarski(X14),k1_tarski(X14)) = k5_xboole_0(k1_tarski(X14),k1_xboole_0) ),
    inference(superposition,[],[f427,f105])).

fof(f105,plain,(
    ! [X13] : k1_xboole_0 = k4_xboole_0(k1_tarski(X13),k1_tarski(X13)) ),
    inference(resolution,[],[f53,f69])).

fof(f69,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_tarski(X0)) ),
    inference(superposition,[],[f66,f40])).

fof(f66,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f427,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f416,f129])).

fof(f129,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f46,f42])).

fof(f416,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f55,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f55,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f3616,plain,(
    k2_tarski(sK0,sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f308,f3615])).

fof(f3615,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f3608,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f3608,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK0 = sK1 ),
    inference(superposition,[],[f308,f710])).

fof(f710,plain,(
    ! [X6,X5] :
      ( k2_xboole_0(k1_tarski(X6),k1_tarski(X5)) = k5_xboole_0(k1_tarski(X6),k1_tarski(X5))
      | X5 = X6 ) ),
    inference(superposition,[],[f427,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f51,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f308,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(superposition,[],[f37,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f32])).

fof(f32,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:07:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.50  % (29606)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (29622)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (29611)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (29615)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (29600)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (29609)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (29614)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (29600)Refutation not found, incomplete strategy% (29600)------------------------------
% 0.20/0.52  % (29600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (29600)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (29600)Memory used [KB]: 1663
% 0.20/0.52  % (29600)Time elapsed: 0.104 s
% 0.20/0.52  % (29600)------------------------------
% 0.20/0.52  % (29600)------------------------------
% 0.20/0.52  % (29627)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (29603)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (29607)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (29610)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (29621)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (29615)Refutation not found, incomplete strategy% (29615)------------------------------
% 0.20/0.52  % (29615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (29615)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (29615)Memory used [KB]: 6140
% 0.20/0.52  % (29615)Time elapsed: 0.003 s
% 0.20/0.52  % (29615)------------------------------
% 0.20/0.52  % (29615)------------------------------
% 0.20/0.52  % (29621)Refutation not found, incomplete strategy% (29621)------------------------------
% 0.20/0.52  % (29621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (29621)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (29621)Memory used [KB]: 1791
% 0.20/0.52  % (29621)Time elapsed: 0.076 s
% 0.20/0.52  % (29621)------------------------------
% 0.20/0.52  % (29621)------------------------------
% 0.20/0.53  % (29605)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (29604)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (29629)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (29611)Refutation not found, incomplete strategy% (29611)------------------------------
% 0.20/0.53  % (29611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (29611)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (29611)Memory used [KB]: 10618
% 0.20/0.53  % (29611)Time elapsed: 0.124 s
% 0.20/0.53  % (29611)------------------------------
% 0.20/0.53  % (29611)------------------------------
% 0.20/0.53  % (29602)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (29602)Refutation not found, incomplete strategy% (29602)------------------------------
% 0.20/0.53  % (29602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (29601)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (29622)Refutation not found, incomplete strategy% (29622)------------------------------
% 0.20/0.54  % (29622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (29610)Refutation not found, incomplete strategy% (29610)------------------------------
% 0.20/0.54  % (29610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (29610)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (29610)Memory used [KB]: 10618
% 0.20/0.54  % (29610)Time elapsed: 0.125 s
% 0.20/0.54  % (29610)------------------------------
% 0.20/0.54  % (29610)------------------------------
% 0.20/0.54  % (29622)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (29622)Memory used [KB]: 10746
% 0.20/0.54  % (29622)Time elapsed: 0.125 s
% 0.20/0.54  % (29622)------------------------------
% 0.20/0.54  % (29622)------------------------------
% 0.20/0.54  % (29620)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (29613)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (29620)Refutation not found, incomplete strategy% (29620)------------------------------
% 0.20/0.54  % (29620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (29620)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (29620)Memory used [KB]: 10746
% 0.20/0.54  % (29620)Time elapsed: 0.130 s
% 0.20/0.54  % (29620)------------------------------
% 0.20/0.54  % (29620)------------------------------
% 0.20/0.54  % (29619)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (29628)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (29623)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (29624)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.48/0.55  % (29602)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (29602)Memory used [KB]: 10746
% 1.48/0.55  % (29602)Time elapsed: 0.128 s
% 1.48/0.55  % (29602)------------------------------
% 1.48/0.55  % (29602)------------------------------
% 1.48/0.55  % (29608)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.48/0.55  % (29626)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.48/0.55  % (29608)Refutation not found, incomplete strategy% (29608)------------------------------
% 1.48/0.55  % (29608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (29608)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (29608)Memory used [KB]: 10746
% 1.48/0.55  % (29608)Time elapsed: 0.127 s
% 1.48/0.55  % (29608)------------------------------
% 1.48/0.55  % (29608)------------------------------
% 1.48/0.55  % (29618)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.48/0.55  % (29612)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.55  % (29616)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.48/0.55  % (29625)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.48/0.56  % (29617)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.48/0.56  % (29617)Refutation not found, incomplete strategy% (29617)------------------------------
% 1.48/0.56  % (29617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (29617)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (29617)Memory used [KB]: 10618
% 1.48/0.56  % (29617)Time elapsed: 0.151 s
% 1.48/0.56  % (29617)------------------------------
% 1.48/0.56  % (29617)------------------------------
% 1.62/0.62  % (29631)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.04/0.65  % (29637)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.19/0.66  % (29633)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.19/0.67  % (29634)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.19/0.67  % (29636)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.19/0.67  % (29601)Refutation not found, incomplete strategy% (29601)------------------------------
% 2.19/0.67  % (29601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.67  % (29601)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.67  
% 2.19/0.67  % (29601)Memory used [KB]: 6268
% 2.19/0.67  % (29601)Time elapsed: 0.219 s
% 2.19/0.67  % (29601)------------------------------
% 2.19/0.67  % (29601)------------------------------
% 2.19/0.68  % (29632)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.19/0.70  % (29639)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.19/0.70  % (29638)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.19/0.70  % (29640)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.19/0.71  % (29635)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.19/0.72  % (29607)Refutation found. Thanks to Tanya!
% 2.19/0.72  % SZS status Theorem for theBenchmark
% 2.19/0.72  % SZS output start Proof for theBenchmark
% 2.19/0.72  fof(f3619,plain,(
% 2.19/0.72    $false),
% 2.19/0.72    inference(subsumption_resolution,[],[f3618,f40])).
% 2.19/0.72  fof(f40,plain,(
% 2.19/0.72    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.19/0.72    inference(cnf_transformation,[],[f11])).
% 2.19/0.72  fof(f11,axiom,(
% 2.19/0.72    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.19/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.19/0.72  fof(f3618,plain,(
% 2.19/0.72    k1_tarski(sK0) != k2_tarski(sK0,sK0)),
% 2.19/0.72    inference(forward_demodulation,[],[f3616,f452])).
% 2.19/0.72  fof(f452,plain,(
% 2.19/0.72    ( ! [X14] : (k1_tarski(X14) = k2_xboole_0(k1_tarski(X14),k1_tarski(X14))) )),
% 2.19/0.72    inference(forward_demodulation,[],[f437,f135])).
% 2.19/0.72  fof(f135,plain,(
% 2.19/0.72    ( ! [X4] : (k5_xboole_0(X4,k1_xboole_0) = X4) )),
% 2.19/0.72    inference(forward_demodulation,[],[f131,f39])).
% 2.19/0.72  fof(f39,plain,(
% 2.19/0.72    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.19/0.72    inference(cnf_transformation,[],[f7])).
% 2.19/0.72  fof(f7,axiom,(
% 2.19/0.72    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.19/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.19/0.72  fof(f131,plain,(
% 2.19/0.72    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k1_xboole_0)) )),
% 2.19/0.72    inference(superposition,[],[f46,f84])).
% 2.19/0.72  fof(f84,plain,(
% 2.19/0.72    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 2.19/0.72    inference(superposition,[],[f77,f42])).
% 2.19/0.72  fof(f42,plain,(
% 2.19/0.72    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.19/0.72    inference(cnf_transformation,[],[f1])).
% 2.19/0.72  fof(f1,axiom,(
% 2.19/0.72    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.19/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.19/0.72  fof(f77,plain,(
% 2.19/0.72    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 2.19/0.72    inference(resolution,[],[f50,f38])).
% 2.19/0.72  fof(f38,plain,(
% 2.19/0.72    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.19/0.72    inference(cnf_transformation,[],[f6])).
% 2.19/0.72  fof(f6,axiom,(
% 2.19/0.72    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.19/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.19/0.72  fof(f50,plain,(
% 2.19/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.19/0.72    inference(cnf_transformation,[],[f29])).
% 2.19/0.72  fof(f29,plain,(
% 2.19/0.72    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.19/0.72    inference(ennf_transformation,[],[f5])).
% 2.19/0.72  fof(f5,axiom,(
% 2.19/0.72    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.19/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.19/0.72  fof(f46,plain,(
% 2.19/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.19/0.72    inference(cnf_transformation,[],[f3])).
% 2.19/0.72  fof(f3,axiom,(
% 2.19/0.72    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.19/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.19/0.72  fof(f437,plain,(
% 2.19/0.72    ( ! [X14] : (k2_xboole_0(k1_tarski(X14),k1_tarski(X14)) = k5_xboole_0(k1_tarski(X14),k1_xboole_0)) )),
% 2.19/0.72    inference(superposition,[],[f427,f105])).
% 2.19/0.72  fof(f105,plain,(
% 2.19/0.72    ( ! [X13] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X13),k1_tarski(X13))) )),
% 2.19/0.72    inference(resolution,[],[f53,f69])).
% 2.19/0.72  fof(f69,plain,(
% 2.19/0.72    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_tarski(X0))) )),
% 2.19/0.72    inference(superposition,[],[f66,f40])).
% 2.19/0.72  fof(f66,plain,(
% 2.19/0.72    ( ! [X2,X1] : (r1_tarski(k1_tarski(X2),k2_tarski(X1,X2))) )),
% 2.19/0.72    inference(equality_resolution,[],[f59])).
% 2.19/0.72  fof(f59,plain,(
% 2.19/0.72    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 2.19/0.72    inference(cnf_transformation,[],[f36])).
% 2.19/0.72  fof(f36,plain,(
% 2.19/0.72    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.19/0.72    inference(flattening,[],[f35])).
% 2.19/0.72  fof(f35,plain,(
% 2.19/0.72    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.19/0.72    inference(nnf_transformation,[],[f31])).
% 2.19/0.72  fof(f31,plain,(
% 2.19/0.72    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.19/0.72    inference(ennf_transformation,[],[f18])).
% 2.19/0.72  fof(f18,axiom,(
% 2.19/0.72    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 2.19/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 2.19/0.72  fof(f53,plain,(
% 2.19/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.19/0.72    inference(cnf_transformation,[],[f34])).
% 2.19/0.72  fof(f34,plain,(
% 2.19/0.72    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.19/0.72    inference(nnf_transformation,[],[f2])).
% 2.19/0.72  fof(f2,axiom,(
% 2.19/0.72    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.19/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.19/0.72  fof(f427,plain,(
% 2.19/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.19/0.72    inference(forward_demodulation,[],[f416,f129])).
% 2.19/0.72  fof(f129,plain,(
% 2.19/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 2.19/0.72    inference(superposition,[],[f46,f42])).
% 2.19/0.72  fof(f416,plain,(
% 2.19/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 2.19/0.72    inference(superposition,[],[f55,f47])).
% 2.19/0.72  fof(f47,plain,(
% 2.19/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.19/0.72    inference(cnf_transformation,[],[f10])).
% 2.19/0.72  fof(f10,axiom,(
% 2.19/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.19/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 2.19/0.72  fof(f55,plain,(
% 2.19/0.72    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.19/0.72    inference(cnf_transformation,[],[f9])).
% 2.19/0.72  fof(f9,axiom,(
% 2.19/0.72    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.19/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.19/0.72  fof(f3616,plain,(
% 2.19/0.72    k2_tarski(sK0,sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 2.19/0.72    inference(backward_demodulation,[],[f308,f3615])).
% 2.19/0.72  fof(f3615,plain,(
% 2.19/0.72    sK0 = sK1),
% 2.19/0.72    inference(subsumption_resolution,[],[f3608,f49])).
% 2.19/0.72  fof(f49,plain,(
% 2.19/0.72    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 2.19/0.72    inference(cnf_transformation,[],[f28])).
% 2.19/0.72  fof(f28,plain,(
% 2.19/0.72    ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 2.19/0.72    inference(ennf_transformation,[],[f22])).
% 2.19/0.72  fof(f22,axiom,(
% 2.19/0.72    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 2.19/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 2.19/0.72  fof(f3608,plain,(
% 2.19/0.72    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | sK0 = sK1),
% 2.19/0.72    inference(superposition,[],[f308,f710])).
% 2.19/0.72  fof(f710,plain,(
% 2.19/0.72    ( ! [X6,X5] : (k2_xboole_0(k1_tarski(X6),k1_tarski(X5)) = k5_xboole_0(k1_tarski(X6),k1_tarski(X5)) | X5 = X6) )),
% 2.19/0.72    inference(superposition,[],[f427,f96])).
% 2.19/0.72  fof(f96,plain,(
% 2.19/0.72    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 2.19/0.72    inference(resolution,[],[f51,f48])).
% 2.19/0.72  fof(f48,plain,(
% 2.19/0.72    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 2.19/0.72    inference(cnf_transformation,[],[f27])).
% 2.19/0.72  fof(f27,plain,(
% 2.19/0.72    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 2.19/0.72    inference(ennf_transformation,[],[f20])).
% 2.19/0.72  fof(f20,axiom,(
% 2.19/0.72    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 2.19/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 2.19/0.72  fof(f51,plain,(
% 2.19/0.72    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 2.19/0.72    inference(cnf_transformation,[],[f30])).
% 2.19/0.72  fof(f30,plain,(
% 2.19/0.72    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 2.19/0.72    inference(ennf_transformation,[],[f25])).
% 2.19/0.72  fof(f25,plain,(
% 2.19/0.72    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 2.19/0.72    inference(unused_predicate_definition_removal,[],[f8])).
% 2.19/0.72  fof(f8,axiom,(
% 2.19/0.72    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.19/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.19/0.72  fof(f308,plain,(
% 2.19/0.72    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 2.19/0.72    inference(superposition,[],[f37,f43])).
% 2.19/0.72  fof(f43,plain,(
% 2.19/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.19/0.72    inference(cnf_transformation,[],[f19])).
% 2.19/0.72  fof(f19,axiom,(
% 2.19/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.19/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.19/0.72  fof(f37,plain,(
% 2.19/0.72    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 2.19/0.72    inference(cnf_transformation,[],[f33])).
% 2.19/0.72  fof(f33,plain,(
% 2.19/0.72    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 2.19/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f32])).
% 2.19/0.72  fof(f32,plain,(
% 2.19/0.72    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 2.19/0.72    introduced(choice_axiom,[])).
% 2.19/0.72  fof(f26,plain,(
% 2.19/0.72    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 2.19/0.72    inference(ennf_transformation,[],[f24])).
% 2.19/0.72  fof(f24,negated_conjecture,(
% 2.19/0.72    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 2.19/0.72    inference(negated_conjecture,[],[f23])).
% 2.19/0.72  fof(f23,conjecture,(
% 2.19/0.72    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 2.19/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).
% 2.19/0.72  % SZS output end Proof for theBenchmark
% 2.19/0.72  % (29607)------------------------------
% 2.19/0.72  % (29607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.72  % (29607)Termination reason: Refutation
% 2.19/0.72  
% 2.19/0.72  % (29607)Memory used [KB]: 8315
% 2.19/0.72  % (29607)Time elapsed: 0.273 s
% 2.19/0.72  % (29607)------------------------------
% 2.19/0.72  % (29607)------------------------------
% 2.19/0.72  % (29599)Success in time 0.347 s
%------------------------------------------------------------------------------
