%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 239 expanded)
%              Number of leaves         :   17 (  61 expanded)
%              Depth                    :   20
%              Number of atoms          :   97 ( 410 expanded)
%              Number of equality atoms :   70 ( 205 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(subsumption_resolution,[],[f136,f72])).

fof(f72,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f65,f71])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f70,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f70,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f50,f45])).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f65,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f136,plain,(
    k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    inference(superposition,[],[f130,f44])).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f130,plain,(
    k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f96,f127])).

fof(f127,plain,(
    k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f119,f125])).

fof(f125,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f122,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f122,plain,(
    ! [X1] : k3_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f113,f50])).

fof(f113,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f112,f45])).

fof(f112,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f105,f46])).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f105,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f51,f42])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f119,plain,(
    sK1 = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f118,f43])).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f118,plain,(
    k3_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f111,f113])).

% (23107)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f111,plain,(
    k3_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f51,f95])).

fof(f95,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f91,f94])).

fof(f94,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f92,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r2_xboole_0(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f73,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f73,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f53,f40])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f92,plain,
    ( r2_xboole_0(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f74,f91])).

fof(f74,plain,(
    ! [X2,X1] :
      ( r2_xboole_0(X1,k2_xboole_0(X1,X2))
      | k2_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f53,f47])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f91,plain,(
    k1_xboole_0 = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f90,f39])).

fof(f39,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f90,plain,(
    k3_tarski(k1_xboole_0) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f48,f85])).

fof(f85,plain,(
    k1_xboole_0 = k2_tarski(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | k1_xboole_0 = k2_tarski(sK0,sK1) ),
    inference(resolution,[],[f76,f77])).

fof(f76,plain,
    ( r2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0)
    | k1_xboole_0 = k2_tarski(sK0,sK1) ),
    inference(resolution,[],[f53,f67])).

fof(f67,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f47,f38])).

fof(f38,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f96,plain,(
    k1_xboole_0 = k2_tarski(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f85,f94])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (23108)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.46  % (23108)Refutation not found, incomplete strategy% (23108)------------------------------
% 0.21/0.46  % (23108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (23119)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.47  % (23108)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (23108)Memory used [KB]: 10618
% 0.21/0.47  % (23108)Time elapsed: 0.066 s
% 0.21/0.47  % (23108)------------------------------
% 0.21/0.47  % (23108)------------------------------
% 0.21/0.51  % (23103)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (23103)Refutation not found, incomplete strategy% (23103)------------------------------
% 0.21/0.51  % (23103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23103)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (23103)Memory used [KB]: 6140
% 0.21/0.51  % (23103)Time elapsed: 0.106 s
% 0.21/0.51  % (23103)------------------------------
% 0.21/0.51  % (23103)------------------------------
% 0.21/0.51  % (23101)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (23121)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (23100)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (23117)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (23113)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (23111)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (23123)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (23128)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (23118)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (23125)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (23104)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (23124)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (23102)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (23124)Refutation not found, incomplete strategy% (23124)------------------------------
% 0.21/0.54  % (23124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23124)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23124)Memory used [KB]: 6268
% 0.21/0.54  % (23124)Time elapsed: 0.135 s
% 0.21/0.54  % (23124)------------------------------
% 0.21/0.54  % (23124)------------------------------
% 0.21/0.54  % (23122)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (23101)Refutation not found, incomplete strategy% (23101)------------------------------
% 0.21/0.54  % (23101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23101)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23101)Memory used [KB]: 10746
% 0.21/0.54  % (23101)Time elapsed: 0.136 s
% 0.21/0.54  % (23101)------------------------------
% 0.21/0.54  % (23101)------------------------------
% 0.21/0.54  % (23120)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (23126)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (23120)Refutation not found, incomplete strategy% (23120)------------------------------
% 0.21/0.54  % (23120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23120)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23120)Memory used [KB]: 1791
% 0.21/0.54  % (23120)Time elapsed: 0.138 s
% 0.21/0.54  % (23120)------------------------------
% 0.21/0.54  % (23120)------------------------------
% 0.21/0.54  % (23115)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (23099)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (23121)Refutation not found, incomplete strategy% (23121)------------------------------
% 0.21/0.54  % (23121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23121)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23121)Memory used [KB]: 10746
% 0.21/0.54  % (23121)Time elapsed: 0.110 s
% 0.21/0.54  % (23121)------------------------------
% 0.21/0.54  % (23121)------------------------------
% 0.21/0.54  % (23099)Refutation not found, incomplete strategy% (23099)------------------------------
% 0.21/0.54  % (23099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23099)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23099)Memory used [KB]: 1663
% 0.21/0.54  % (23099)Time elapsed: 0.134 s
% 0.21/0.54  % (23099)------------------------------
% 0.21/0.54  % (23099)------------------------------
% 0.21/0.54  % (23105)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (23114)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (23127)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (23114)Refutation not found, incomplete strategy% (23114)------------------------------
% 0.21/0.54  % (23114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23114)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23114)Memory used [KB]: 6140
% 0.21/0.54  % (23114)Time elapsed: 0.002 s
% 0.21/0.54  % (23114)------------------------------
% 0.21/0.54  % (23114)------------------------------
% 0.21/0.54  % (23106)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (23116)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (23109)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (23116)Refutation not found, incomplete strategy% (23116)------------------------------
% 0.21/0.55  % (23116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (23116)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (23116)Memory used [KB]: 10618
% 0.21/0.55  % (23116)Time elapsed: 0.147 s
% 0.21/0.55  % (23116)------------------------------
% 0.21/0.55  % (23116)------------------------------
% 0.21/0.55  % (23109)Refutation not found, incomplete strategy% (23109)------------------------------
% 0.21/0.55  % (23109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (23109)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (23109)Memory used [KB]: 10618
% 0.21/0.55  % (23109)Time elapsed: 0.149 s
% 0.21/0.55  % (23109)------------------------------
% 0.21/0.55  % (23109)------------------------------
% 0.21/0.55  % (23106)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f136,f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 0.21/0.55    inference(backward_demodulation,[],[f65,f71])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f70,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 0.21/0.55    inference(superposition,[],[f50,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.55    inference(rectify,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.21/0.55    inference(equality_resolution,[],[f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.21/0.55    inference(nnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,axiom,(
% 0.21/0.55    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    k1_xboole_0 = k1_tarski(k1_xboole_0)),
% 0.21/0.55    inference(superposition,[],[f130,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,axiom,(
% 0.21/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.55  fof(f130,plain,(
% 0.21/0.55    k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.55    inference(backward_demodulation,[],[f96,f127])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    k1_xboole_0 = sK1),
% 0.21/0.55    inference(backward_demodulation,[],[f119,f125])).
% 0.21/0.55  fof(f125,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f122,f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    ( ! [X1] : (k3_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1)) )),
% 0.21/0.55    inference(superposition,[],[f113,f50])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.55    inference(forward_demodulation,[],[f112,f45])).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f105,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.55    inference(rectify,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.55  fof(f105,plain,(
% 0.21/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 0.21/0.55    inference(superposition,[],[f51,f42])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    sK1 = k3_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.55    inference(forward_demodulation,[],[f118,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    k3_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.55    inference(forward_demodulation,[],[f111,f113])).
% 0.21/0.55  % (23107)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    k3_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k1_xboole_0)),
% 0.21/0.55    inference(superposition,[],[f51,f95])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.55    inference(backward_demodulation,[],[f91,f94])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    k1_xboole_0 = sK0),
% 0.21/0.55    inference(subsumption_resolution,[],[f92,f77])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_xboole_0(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(resolution,[],[f73,f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(resolution,[],[f53,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(flattening,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.21/0.55    inference(unused_predicate_definition_removal,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    r2_xboole_0(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 0.21/0.55    inference(superposition,[],[f74,f91])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X2,X1] : (r2_xboole_0(X1,k2_xboole_0(X1,X2)) | k2_xboole_0(X1,X2) = X1) )),
% 0.21/0.55    inference(resolution,[],[f53,f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    k1_xboole_0 = k2_xboole_0(sK0,sK1)),
% 0.21/0.55    inference(forward_demodulation,[],[f90,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,axiom,(
% 0.21/0.55    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    k3_tarski(k1_xboole_0) = k2_xboole_0(sK0,sK1)),
% 0.21/0.55    inference(superposition,[],[f48,f85])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    k1_xboole_0 = k2_tarski(sK0,sK1)),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f83])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    k1_xboole_0 = k2_tarski(sK0,sK1) | k1_xboole_0 = k2_tarski(sK0,sK1)),
% 0.21/0.55    inference(resolution,[],[f76,f77])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    r2_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) | k1_xboole_0 = k2_tarski(sK0,sK1)),
% 0.21/0.55    inference(resolution,[],[f53,f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    r1_tarski(k2_tarski(sK0,sK1),k1_xboole_0)),
% 0.21/0.55    inference(superposition,[],[f47,f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.55    inference(ennf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.55    inference(negated_conjecture,[],[f26])).
% 0.21/0.55  fof(f26,conjecture,(
% 0.21/0.55    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    k1_xboole_0 = k2_tarski(k1_xboole_0,sK1)),
% 0.21/0.55    inference(backward_demodulation,[],[f85,f94])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (23106)------------------------------
% 0.21/0.55  % (23106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (23106)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (23106)Memory used [KB]: 6268
% 0.21/0.55  % (23106)Time elapsed: 0.150 s
% 0.21/0.55  % (23106)------------------------------
% 0.21/0.55  % (23106)------------------------------
% 0.21/0.55  % (23098)Success in time 0.188 s
%------------------------------------------------------------------------------
