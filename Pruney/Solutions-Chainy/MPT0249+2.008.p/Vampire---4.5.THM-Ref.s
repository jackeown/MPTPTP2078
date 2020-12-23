%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:11 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 334 expanded)
%              Number of leaves         :   16 (  98 expanded)
%              Depth                    :   27
%              Number of atoms          :  137 ( 821 expanded)
%              Number of equality atoms :   79 ( 553 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2333,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2332,f39])).

fof(f39,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f30])).

fof(f30,plain,
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

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f2332,plain,(
    k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f2326,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f2326,plain,(
    sK2 = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f580,f2305])).

fof(f2305,plain,(
    sK1 = k5_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f2304,f126])).

fof(f126,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f36,f123])).

fof(f123,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f122,f38])).

fof(f38,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f122,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f121,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f121,plain,
    ( v1_xboole_0(sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f115,f68])).

fof(f68,plain,(
    sK1 = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f47,f36])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f115,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f54,f92])).

fof(f92,plain,
    ( r2_hidden(sK0,sK1)
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f79,f68])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k3_xboole_0(X1,k1_tarski(X0)))
      | r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f73,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k3_xboole_0(k1_tarski(X0),X1))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f72,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(k1_tarski(X1),X2))
      | r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f52,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f36,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f2304,plain,(
    k2_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f2300,f41])).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f2300,plain,(
    k2_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(superposition,[],[f50,f2281])).

fof(f2281,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f2254,f37])).

fof(f37,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f2254,plain,
    ( sK1 = sK2
    | k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f1939,f126])).

fof(f1939,plain,(
    ! [X4] :
      ( k2_xboole_0(sK1,X4) = X4
      | k1_xboole_0 = k3_xboole_0(sK1,X4) ) ),
    inference(forward_demodulation,[],[f1915,f628])).

fof(f628,plain,(
    ! [X12,X11] : k5_xboole_0(k5_xboole_0(X12,X11),X12) = X11 ),
    inference(superposition,[],[f593,f593])).

fof(f593,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f580,f46])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1915,plain,(
    ! [X4] :
      ( k2_xboole_0(sK1,X4) = k5_xboole_0(k5_xboole_0(sK1,X4),sK1)
      | k1_xboole_0 = k3_xboole_0(sK1,X4) ) ),
    inference(superposition,[],[f50,f272])).

fof(f272,plain,(
    ! [X1] :
      ( sK1 = k3_xboole_0(sK1,X1)
      | k1_xboole_0 = k3_xboole_0(sK1,X1) ) ),
    inference(superposition,[],[f185,f45])).

fof(f185,plain,(
    ! [X6] :
      ( sK1 = k3_xboole_0(X6,sK1)
      | k1_xboole_0 = k3_xboole_0(sK1,X6) ) ),
    inference(forward_demodulation,[],[f184,f123])).

fof(f184,plain,(
    ! [X6] :
      ( k1_xboole_0 = k3_xboole_0(sK1,X6)
      | k1_tarski(sK0) = k3_xboole_0(X6,k1_tarski(sK0)) ) ),
    inference(resolution,[],[f145,f54])).

fof(f145,plain,(
    ! [X0] :
      ( r2_hidden(sK0,X0)
      | k1_xboole_0 = k3_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f132,f43])).

fof(f132,plain,(
    ! [X3] :
      ( v1_xboole_0(k3_xboole_0(sK1,X3))
      | r2_hidden(sK0,X3) ) ),
    inference(superposition,[],[f73,f123])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f580,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f549,f60])).

fof(f60,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f46,f41])).

fof(f549,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f56,f40])).

fof(f56,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:46:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (22096)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.49  % (22103)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.49  % (22111)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.49  % (22111)Refutation not found, incomplete strategy% (22111)------------------------------
% 0.19/0.49  % (22111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (22098)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.49  % (22111)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (22111)Memory used [KB]: 6140
% 0.19/0.49  % (22111)Time elapsed: 0.094 s
% 0.19/0.49  % (22111)------------------------------
% 0.19/0.49  % (22111)------------------------------
% 0.19/0.50  % (22104)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.50  % (22099)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.50  % (22115)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.51  % (22119)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.51  % (22109)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.51  % (22102)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.51  % (22107)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.51  % (22100)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.51  % (22110)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.51  % (22097)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.52  % (22125)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.52  % (22118)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.52  % (22122)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.52  % (22108)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (22117)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.52  % (22120)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.52  % (22113)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.52  % (22112)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.52  % (22113)Refutation not found, incomplete strategy% (22113)------------------------------
% 0.19/0.52  % (22113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (22114)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.52  % (22113)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (22113)Memory used [KB]: 10618
% 0.19/0.52  % (22113)Time elapsed: 0.129 s
% 0.19/0.52  % (22113)------------------------------
% 0.19/0.52  % (22113)------------------------------
% 0.19/0.53  % (22101)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.53  % (22121)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.53  % (22106)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.53  % (22124)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.53  % (22105)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.53  % (22123)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.54  % (22116)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.73/0.60  % (22103)Refutation found. Thanks to Tanya!
% 1.73/0.60  % SZS status Theorem for theBenchmark
% 1.73/0.60  % SZS output start Proof for theBenchmark
% 1.73/0.60  fof(f2333,plain,(
% 1.73/0.60    $false),
% 1.73/0.60    inference(subsumption_resolution,[],[f2332,f39])).
% 1.73/0.60  fof(f39,plain,(
% 1.73/0.60    k1_xboole_0 != sK2),
% 1.73/0.60    inference(cnf_transformation,[],[f31])).
% 1.73/0.60  fof(f31,plain,(
% 1.73/0.60    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.73/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f30])).
% 1.73/0.60  fof(f30,plain,(
% 1.73/0.60    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.73/0.60    introduced(choice_axiom,[])).
% 1.73/0.60  fof(f24,plain,(
% 1.73/0.60    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.73/0.60    inference(ennf_transformation,[],[f21])).
% 1.73/0.60  fof(f21,negated_conjecture,(
% 1.73/0.60    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.73/0.60    inference(negated_conjecture,[],[f20])).
% 1.73/0.60  fof(f20,conjecture,(
% 1.73/0.60    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.73/0.60  fof(f2332,plain,(
% 1.73/0.60    k1_xboole_0 = sK2),
% 1.73/0.60    inference(forward_demodulation,[],[f2326,f40])).
% 1.73/0.60  fof(f40,plain,(
% 1.73/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f9])).
% 1.73/0.60  fof(f9,axiom,(
% 1.73/0.60    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.73/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.73/0.60  fof(f2326,plain,(
% 1.73/0.60    sK2 = k5_xboole_0(sK1,sK1)),
% 1.73/0.60    inference(superposition,[],[f580,f2305])).
% 1.73/0.60  fof(f2305,plain,(
% 1.73/0.60    sK1 = k5_xboole_0(sK1,sK2)),
% 1.73/0.60    inference(forward_demodulation,[],[f2304,f126])).
% 1.73/0.60  fof(f126,plain,(
% 1.73/0.60    sK1 = k2_xboole_0(sK1,sK2)),
% 1.73/0.60    inference(backward_demodulation,[],[f36,f123])).
% 1.73/0.60  fof(f123,plain,(
% 1.73/0.60    sK1 = k1_tarski(sK0)),
% 1.73/0.60    inference(subsumption_resolution,[],[f122,f38])).
% 1.73/0.60  fof(f38,plain,(
% 1.73/0.60    k1_xboole_0 != sK1),
% 1.73/0.60    inference(cnf_transformation,[],[f31])).
% 1.73/0.60  fof(f122,plain,(
% 1.73/0.60    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 1.73/0.60    inference(resolution,[],[f121,f43])).
% 1.73/0.61  fof(f43,plain,(
% 1.73/0.61    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.73/0.61    inference(cnf_transformation,[],[f25])).
% 1.73/0.61  fof(f25,plain,(
% 1.73/0.61    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.73/0.61    inference(ennf_transformation,[],[f4])).
% 1.73/0.61  fof(f4,axiom,(
% 1.73/0.61    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.73/0.61  fof(f121,plain,(
% 1.73/0.61    v1_xboole_0(sK1) | sK1 = k1_tarski(sK0)),
% 1.73/0.61    inference(forward_demodulation,[],[f115,f68])).
% 1.73/0.61  fof(f68,plain,(
% 1.73/0.61    sK1 = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.73/0.61    inference(superposition,[],[f47,f36])).
% 1.73/0.61  fof(f47,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.73/0.61    inference(cnf_transformation,[],[f6])).
% 1.73/0.61  fof(f6,axiom,(
% 1.73/0.61    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.73/0.61  fof(f115,plain,(
% 1.73/0.61    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) | v1_xboole_0(sK1)),
% 1.73/0.61    inference(resolution,[],[f54,f92])).
% 1.73/0.61  fof(f92,plain,(
% 1.73/0.61    r2_hidden(sK0,sK1) | v1_xboole_0(sK1)),
% 1.73/0.61    inference(superposition,[],[f79,f68])).
% 1.73/0.61  fof(f79,plain,(
% 1.73/0.61    ( ! [X0,X1] : (v1_xboole_0(k3_xboole_0(X1,k1_tarski(X0))) | r2_hidden(X0,X1)) )),
% 1.73/0.61    inference(superposition,[],[f73,f45])).
% 1.73/0.61  fof(f45,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f1])).
% 1.73/0.61  fof(f1,axiom,(
% 1.73/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.73/0.61  fof(f73,plain,(
% 1.73/0.61    ( ! [X0,X1] : (v1_xboole_0(k3_xboole_0(k1_tarski(X0),X1)) | r2_hidden(X0,X1)) )),
% 1.73/0.61    inference(resolution,[],[f72,f44])).
% 1.73/0.61  fof(f44,plain,(
% 1.73/0.61    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f33])).
% 1.73/0.61  fof(f33,plain,(
% 1.73/0.61    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0))),
% 1.73/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f32])).
% 1.73/0.61  fof(f32,plain,(
% 1.73/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.73/0.61    introduced(choice_axiom,[])).
% 1.73/0.61  fof(f26,plain,(
% 1.73/0.61    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 1.73/0.61    inference(ennf_transformation,[],[f23])).
% 1.73/0.61  fof(f23,plain,(
% 1.73/0.61    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 1.73/0.61    inference(unused_predicate_definition_removal,[],[f3])).
% 1.73/0.61  fof(f3,axiom,(
% 1.73/0.61    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.73/0.61  fof(f72,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(k1_tarski(X1),X2)) | r2_hidden(X1,X2)) )),
% 1.73/0.61    inference(resolution,[],[f52,f53])).
% 1.73/0.61  fof(f53,plain,(
% 1.73/0.61    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f28])).
% 1.73/0.61  fof(f28,plain,(
% 1.73/0.61    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.73/0.61    inference(ennf_transformation,[],[f17])).
% 1.73/0.61  fof(f17,axiom,(
% 1.73/0.61    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.73/0.61  fof(f52,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.73/0.61    inference(cnf_transformation,[],[f35])).
% 1.73/0.61  fof(f35,plain,(
% 1.73/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.73/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f34])).
% 1.73/0.61  fof(f34,plain,(
% 1.73/0.61    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.73/0.61    introduced(choice_axiom,[])).
% 1.73/0.61  fof(f27,plain,(
% 1.73/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.73/0.61    inference(ennf_transformation,[],[f22])).
% 1.73/0.61  fof(f22,plain,(
% 1.73/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.73/0.61    inference(rectify,[],[f5])).
% 1.73/0.61  fof(f5,axiom,(
% 1.73/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.73/0.61  fof(f54,plain,(
% 1.73/0.61    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))) )),
% 1.73/0.61    inference(cnf_transformation,[],[f29])).
% 1.73/0.61  fof(f29,plain,(
% 1.73/0.61    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 1.73/0.61    inference(ennf_transformation,[],[f18])).
% 1.73/0.61  fof(f18,axiom,(
% 1.73/0.61    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 1.73/0.61  fof(f36,plain,(
% 1.73/0.61    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.73/0.61    inference(cnf_transformation,[],[f31])).
% 1.73/0.61  fof(f2304,plain,(
% 1.73/0.61    k2_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK2)),
% 1.73/0.61    inference(forward_demodulation,[],[f2300,f41])).
% 1.73/0.61  fof(f41,plain,(
% 1.73/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.73/0.61    inference(cnf_transformation,[],[f7])).
% 1.73/0.61  fof(f7,axiom,(
% 1.73/0.61    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.73/0.61  fof(f2300,plain,(
% 1.73/0.61    k2_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_xboole_0)),
% 1.73/0.61    inference(superposition,[],[f50,f2281])).
% 1.73/0.61  fof(f2281,plain,(
% 1.73/0.61    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.73/0.61    inference(subsumption_resolution,[],[f2254,f37])).
% 1.73/0.61  fof(f37,plain,(
% 1.73/0.61    sK1 != sK2),
% 1.73/0.61    inference(cnf_transformation,[],[f31])).
% 1.73/0.61  fof(f2254,plain,(
% 1.73/0.61    sK1 = sK2 | k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.73/0.61    inference(superposition,[],[f1939,f126])).
% 1.73/0.61  fof(f1939,plain,(
% 1.73/0.61    ( ! [X4] : (k2_xboole_0(sK1,X4) = X4 | k1_xboole_0 = k3_xboole_0(sK1,X4)) )),
% 1.73/0.61    inference(forward_demodulation,[],[f1915,f628])).
% 1.73/0.61  fof(f628,plain,(
% 1.73/0.61    ( ! [X12,X11] : (k5_xboole_0(k5_xboole_0(X12,X11),X12) = X11) )),
% 1.73/0.61    inference(superposition,[],[f593,f593])).
% 1.73/0.61  fof(f593,plain,(
% 1.73/0.61    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 1.73/0.61    inference(superposition,[],[f580,f46])).
% 1.73/0.61  fof(f46,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.73/0.61    inference(cnf_transformation,[],[f2])).
% 1.73/0.61  fof(f2,axiom,(
% 1.73/0.61    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.73/0.61  fof(f1915,plain,(
% 1.73/0.61    ( ! [X4] : (k2_xboole_0(sK1,X4) = k5_xboole_0(k5_xboole_0(sK1,X4),sK1) | k1_xboole_0 = k3_xboole_0(sK1,X4)) )),
% 1.73/0.61    inference(superposition,[],[f50,f272])).
% 1.73/0.61  fof(f272,plain,(
% 1.73/0.61    ( ! [X1] : (sK1 = k3_xboole_0(sK1,X1) | k1_xboole_0 = k3_xboole_0(sK1,X1)) )),
% 1.73/0.61    inference(superposition,[],[f185,f45])).
% 1.73/0.61  fof(f185,plain,(
% 1.73/0.61    ( ! [X6] : (sK1 = k3_xboole_0(X6,sK1) | k1_xboole_0 = k3_xboole_0(sK1,X6)) )),
% 1.73/0.61    inference(forward_demodulation,[],[f184,f123])).
% 1.73/0.61  fof(f184,plain,(
% 1.73/0.61    ( ! [X6] : (k1_xboole_0 = k3_xboole_0(sK1,X6) | k1_tarski(sK0) = k3_xboole_0(X6,k1_tarski(sK0))) )),
% 1.73/0.61    inference(resolution,[],[f145,f54])).
% 1.73/0.61  fof(f145,plain,(
% 1.73/0.61    ( ! [X0] : (r2_hidden(sK0,X0) | k1_xboole_0 = k3_xboole_0(sK1,X0)) )),
% 1.73/0.61    inference(resolution,[],[f132,f43])).
% 1.73/0.61  fof(f132,plain,(
% 1.73/0.61    ( ! [X3] : (v1_xboole_0(k3_xboole_0(sK1,X3)) | r2_hidden(sK0,X3)) )),
% 1.73/0.61    inference(superposition,[],[f73,f123])).
% 1.73/0.61  fof(f50,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.73/0.61    inference(cnf_transformation,[],[f10])).
% 1.73/0.61  fof(f10,axiom,(
% 1.73/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.73/0.61  fof(f580,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.73/0.61    inference(forward_demodulation,[],[f549,f60])).
% 1.73/0.61  fof(f60,plain,(
% 1.73/0.61    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.73/0.61    inference(superposition,[],[f46,f41])).
% 1.73/0.61  fof(f549,plain,(
% 1.73/0.61    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.73/0.61    inference(superposition,[],[f56,f40])).
% 1.73/0.61  fof(f56,plain,(
% 1.73/0.61    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.73/0.61    inference(cnf_transformation,[],[f8])).
% 1.73/0.61  fof(f8,axiom,(
% 1.73/0.61    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.73/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.73/0.61  % SZS output end Proof for theBenchmark
% 1.73/0.61  % (22103)------------------------------
% 1.73/0.61  % (22103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.61  % (22103)Termination reason: Refutation
% 1.73/0.61  
% 1.73/0.61  % (22103)Memory used [KB]: 7291
% 1.73/0.61  % (22103)Time elapsed: 0.203 s
% 1.73/0.61  % (22103)------------------------------
% 1.73/0.61  % (22103)------------------------------
% 1.73/0.61  % (22095)Success in time 0.259 s
%------------------------------------------------------------------------------
