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
% DateTime   : Thu Dec  3 12:48:48 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 130 expanded)
%              Number of leaves         :   14 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  121 ( 262 expanded)
%              Number of equality atoms :   63 ( 145 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f117])).

fof(f117,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f116,f104])).

fof(f104,plain,(
    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f97,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

fof(f97,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f96,f56])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK2(X4),sK3(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f36,f38,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK2(X4),sK3(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f96,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f63,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) ),
    inference(definition_unfolding,[],[f45,f60])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k2_tarski(X1,X1)))) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f52,f60,f58])).

fof(f58,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f116,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f40,f115])).

fof(f115,plain,(
    k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f113])).

fof(f113,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f40,f112])).

fof(f112,plain,(
    ! [X4] :
      ( k1_xboole_0 = k7_relat_1(k1_xboole_0,X4)
      | k1_xboole_0 = X4 ) ),
    inference(forward_demodulation,[],[f111,f104])).

fof(f111,plain,(
    ! [X4] :
      ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0),X4)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f108,f97])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,k1_xboole_0) = k7_relat_1(k7_relat_1(X1,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f100,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

fof(f100,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X4)
      | ~ r2_xboole_0(X2,X3)
      | k7_relat_1(X4,X2) = k7_relat_1(k7_relat_1(X4,X2),X3) ) ),
    inference(resolution,[],[f41,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

fof(f40,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f28])).

fof(f28,plain,
    ( ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:33 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (25310)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (25307)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (25307)Refutation not found, incomplete strategy% (25307)------------------------------
% 0.21/0.51  % (25307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (25307)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (25307)Memory used [KB]: 1663
% 0.21/0.51  % (25307)Time elapsed: 0.107 s
% 0.21/0.51  % (25307)------------------------------
% 0.21/0.51  % (25307)------------------------------
% 0.21/0.52  % (25326)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (25326)Refutation not found, incomplete strategy% (25326)------------------------------
% 0.21/0.52  % (25326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (25317)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (25326)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (25326)Memory used [KB]: 1663
% 0.21/0.52  % (25326)Time elapsed: 0.112 s
% 0.21/0.52  % (25326)------------------------------
% 0.21/0.52  % (25326)------------------------------
% 0.21/0.52  % (25306)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (25327)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (25311)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (25335)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (25317)Refutation not found, incomplete strategy% (25317)------------------------------
% 0.21/0.53  % (25317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (25335)Refutation not found, incomplete strategy% (25335)------------------------------
% 1.32/0.53  % (25335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (25335)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (25335)Memory used [KB]: 6140
% 1.32/0.53  % (25335)Time elapsed: 0.122 s
% 1.32/0.53  % (25335)------------------------------
% 1.32/0.53  % (25335)------------------------------
% 1.32/0.53  % (25311)Refutation found. Thanks to Tanya!
% 1.32/0.53  % SZS status Theorem for theBenchmark
% 1.32/0.53  % (25317)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (25317)Memory used [KB]: 10618
% 1.32/0.53  % (25317)Time elapsed: 0.112 s
% 1.32/0.53  % (25317)------------------------------
% 1.32/0.53  % (25317)------------------------------
% 1.32/0.53  % SZS output start Proof for theBenchmark
% 1.32/0.53  fof(f119,plain,(
% 1.32/0.53    $false),
% 1.32/0.53    inference(trivial_inequality_removal,[],[f117])).
% 1.32/0.53  fof(f117,plain,(
% 1.32/0.53    k1_xboole_0 != k1_xboole_0),
% 1.32/0.53    inference(superposition,[],[f116,f104])).
% 1.32/0.53  fof(f104,plain,(
% 1.32/0.53    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.32/0.53    inference(resolution,[],[f97,f43])).
% 1.32/0.53  fof(f43,plain,(
% 1.32/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f25])).
% 1.32/0.53  fof(f25,plain,(
% 1.32/0.53    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 1.32/0.53    inference(ennf_transformation,[],[f18])).
% 1.32/0.53  fof(f18,axiom,(
% 1.32/0.53    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).
% 1.32/0.53  fof(f97,plain,(
% 1.32/0.53    v1_relat_1(k1_xboole_0)),
% 1.32/0.53    inference(resolution,[],[f96,f56])).
% 1.32/0.53  fof(f56,plain,(
% 1.32/0.53    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f39])).
% 1.32/0.53  fof(f39,plain,(
% 1.32/0.53    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0))) & (! [X4] : (k4_tarski(sK2(X4),sK3(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f36,f38,f37])).
% 1.32/0.53  fof(f37,plain,(
% 1.32/0.53    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f38,plain,(
% 1.32/0.53    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK2(X4),sK3(X4)) = X4)),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f36,plain,(
% 1.32/0.53    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 1.32/0.53    inference(rectify,[],[f35])).
% 1.32/0.53  fof(f35,plain,(
% 1.32/0.53    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 1.32/0.53    inference(nnf_transformation,[],[f27])).
% 1.32/0.53  fof(f27,plain,(
% 1.32/0.53    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 1.32/0.53    inference(ennf_transformation,[],[f15])).
% 1.32/0.53  fof(f15,axiom,(
% 1.32/0.53    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 1.32/0.53  fof(f96,plain,(
% 1.32/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.32/0.53    inference(trivial_inequality_removal,[],[f95])).
% 1.32/0.53  fof(f95,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.32/0.53    inference(superposition,[],[f63,f61])).
% 1.32/0.53  fof(f61,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0)))) )),
% 1.32/0.53    inference(definition_unfolding,[],[f45,f60])).
% 1.32/0.53  fof(f60,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.32/0.53    inference(definition_unfolding,[],[f54,f59])).
% 1.32/0.53  fof(f59,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f14])).
% 1.32/0.53  fof(f14,axiom,(
% 1.32/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.32/0.53  fof(f54,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f3])).
% 1.32/0.53  fof(f3,axiom,(
% 1.32/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.32/0.53  fof(f45,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f4])).
% 1.32/0.53  fof(f4,axiom,(
% 1.32/0.53    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.32/0.53  fof(f63,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k2_tarski(X1,X1)))) != X0 | ~r2_hidden(X1,X0)) )),
% 1.32/0.53    inference(definition_unfolding,[],[f52,f60,f58])).
% 1.32/0.53  fof(f58,plain,(
% 1.32/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f6])).
% 1.32/0.53  fof(f6,axiom,(
% 1.32/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.32/0.53  fof(f52,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.32/0.53    inference(cnf_transformation,[],[f34])).
% 1.32/0.53  fof(f34,plain,(
% 1.32/0.53    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.32/0.53    inference(nnf_transformation,[],[f13])).
% 1.32/0.53  fof(f13,axiom,(
% 1.32/0.53    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.32/0.53  fof(f116,plain,(
% 1.32/0.53    k1_xboole_0 != k7_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.32/0.53    inference(backward_demodulation,[],[f40,f115])).
% 1.32/0.53  fof(f115,plain,(
% 1.32/0.53    k1_xboole_0 = sK0),
% 1.32/0.53    inference(trivial_inequality_removal,[],[f113])).
% 1.32/0.53  fof(f113,plain,(
% 1.32/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 1.32/0.53    inference(superposition,[],[f40,f112])).
% 1.32/0.53  fof(f112,plain,(
% 1.32/0.53    ( ! [X4] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X4) | k1_xboole_0 = X4) )),
% 1.32/0.53    inference(forward_demodulation,[],[f111,f104])).
% 1.32/0.53  fof(f111,plain,(
% 1.32/0.53    ( ! [X4] : (k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0),X4) | k1_xboole_0 = X4) )),
% 1.32/0.53    inference(resolution,[],[f108,f97])).
% 1.32/0.53  fof(f108,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,k1_xboole_0) = k7_relat_1(k7_relat_1(X1,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 1.32/0.53    inference(resolution,[],[f100,f44])).
% 1.32/0.53  fof(f44,plain,(
% 1.32/0.53    ( ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 1.32/0.53    inference(cnf_transformation,[],[f26])).
% 1.32/0.53  fof(f26,plain,(
% 1.32/0.53    ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0)),
% 1.32/0.53    inference(ennf_transformation,[],[f5])).
% 1.32/0.53  fof(f5,axiom,(
% 1.32/0.53    ! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).
% 1.32/0.53  fof(f100,plain,(
% 1.32/0.53    ( ! [X4,X2,X3] : (~v1_relat_1(X4) | ~r2_xboole_0(X2,X3) | k7_relat_1(X4,X2) = k7_relat_1(k7_relat_1(X4,X2),X3)) )),
% 1.32/0.53    inference(resolution,[],[f41,f46])).
% 1.32/0.53  fof(f46,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f31])).
% 1.32/0.53  fof(f31,plain,(
% 1.32/0.53    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.32/0.53    inference(flattening,[],[f30])).
% 1.32/0.53  fof(f30,plain,(
% 1.32/0.53    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.32/0.53    inference(nnf_transformation,[],[f1])).
% 1.32/0.53  fof(f1,axiom,(
% 1.32/0.53    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.32/0.53  fof(f41,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X2) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f23])).
% 1.32/0.53  fof(f23,plain,(
% 1.32/0.53    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.32/0.53    inference(flattening,[],[f22])).
% 1.32/0.53  fof(f22,plain,(
% 1.32/0.53    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.32/0.53    inference(ennf_transformation,[],[f17])).
% 1.32/0.53  fof(f17,axiom,(
% 1.32/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).
% 1.32/0.53  fof(f40,plain,(
% 1.32/0.53    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 1.32/0.53    inference(cnf_transformation,[],[f29])).
% 1.32/0.53  fof(f29,plain,(
% 1.32/0.53    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f28])).
% 1.32/0.53  fof(f28,plain,(
% 1.32/0.53    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f21,plain,(
% 1.32/0.53    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)),
% 1.32/0.53    inference(ennf_transformation,[],[f20])).
% 1.32/0.53  fof(f20,negated_conjecture,(
% 1.32/0.53    ~! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 1.32/0.53    inference(negated_conjecture,[],[f19])).
% 1.32/0.53  fof(f19,conjecture,(
% 1.32/0.53    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 1.32/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).
% 1.32/0.53  % SZS output end Proof for theBenchmark
% 1.32/0.53  % (25311)------------------------------
% 1.32/0.53  % (25311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (25311)Termination reason: Refutation
% 1.32/0.53  
% 1.32/0.53  % (25311)Memory used [KB]: 1663
% 1.32/0.53  % (25311)Time elapsed: 0.116 s
% 1.32/0.53  % (25311)------------------------------
% 1.32/0.53  % (25311)------------------------------
% 1.32/0.53  % (25308)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.32/0.53  % (25303)Success in time 0.171 s
%------------------------------------------------------------------------------
