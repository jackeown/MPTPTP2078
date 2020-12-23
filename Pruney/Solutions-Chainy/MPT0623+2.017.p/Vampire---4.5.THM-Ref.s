%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 221 expanded)
%              Number of leaves         :    9 (  53 expanded)
%              Depth                    :   21
%              Number of atoms          :  177 ( 751 expanded)
%              Number of equality atoms :   99 ( 393 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f130,plain,(
    $false ),
    inference(subsumption_resolution,[],[f129,f77])).

fof(f77,plain,(
    k1_xboole_0 != sK1 ),
    inference(subsumption_resolution,[],[f76,f69])).

fof(f69,plain,(
    ! [X3] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != X3 ) ),
    inference(superposition,[],[f30,f65])).

fof(f65,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3(X0)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f53,f32])).

fof(f32,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(sK3(X0))
      | k1_xboole_0 = sK3(X0) ) ),
    inference(resolution,[],[f23,f30])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f30,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f76,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f75,f68])).

fof(f68,plain,(
    ! [X2] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != X2 ) ),
    inference(superposition,[],[f31,f65])).

fof(f31,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f75,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f74,f20])).

fof(f20,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f74,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != sK1
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f73,f22])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f73,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != sK1
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f18,f21])).

fof(f21,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f129,plain,(
    k1_xboole_0 = sK1 ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X5] :
      ( sK1 != X5
      | k1_xboole_0 = X5 ) ),
    inference(global_subsumption,[],[f19,f77,f127])).

fof(f127,plain,(
    ! [X5] :
      ( sK1 != X5
      | k1_xboole_0 = X5
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f124,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f35,f22])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f124,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK0,X1)
      | sK1 != X0
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | r1_tarski(sK0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f119,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f119,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK2(X1,sK4(sK0,X0)))
      | r1_tarski(sK0,X0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f118,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | sK1 != k1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f80,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | sK1 != k1_relat_1(sK2(X0,X1))
      | ~ v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f78,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK0)
      | ~ v1_funct_1(sK2(X0,X1))
      | sK1 != k1_relat_1(sK2(X0,X1))
      | ~ v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f18,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f118,plain,(
    ! [X1] :
      ( r1_tarski(k1_tarski(sK4(sK0,X1)),sK0)
      | r1_tarski(sK0,X1) ) ),
    inference(resolution,[],[f115,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f115,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r1_tarski(k1_tarski(X0),sK0) ) ),
    inference(superposition,[],[f38,f113])).

fof(f113,plain,(
    ! [X0] : sK4(k1_tarski(X0),sK0) = X0 ),
    inference(subsumption_resolution,[],[f112,f77])).

fof(f112,plain,(
    ! [X0] :
      ( sK4(k1_tarski(X0),sK0) = X0
      | k1_xboole_0 = sK1 ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK4(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK4(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f84,f27])).

fof(f84,plain,(
    ! [X2,X3] :
      ( sK1 != k1_relat_1(sK2(X3,X2))
      | sK4(k1_tarski(X2),sK0) = X2
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f50,f81])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | sK4(k1_tarski(X0),X1) = X0 ) ),
    inference(resolution,[],[f37,f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f19,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:21:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (23969)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (23969)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % (23980)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.57  % (23963)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.57  % (23972)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.57  % (23972)Refutation not found, incomplete strategy% (23972)------------------------------
% 0.22/0.57  % (23972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (23986)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.57  % (23980)Refutation not found, incomplete strategy% (23980)------------------------------
% 0.22/0.57  % (23980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.58  % (23977)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.49/0.58  % (23978)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.49/0.58  % (23972)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.58  
% 1.49/0.58  % (23972)Memory used [KB]: 10618
% 1.49/0.58  % (23972)Time elapsed: 0.144 s
% 1.49/0.58  % (23972)------------------------------
% 1.49/0.58  % (23972)------------------------------
% 1.49/0.58  % (23976)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.49/0.58  % (23980)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.58  
% 1.49/0.58  % (23980)Memory used [KB]: 10618
% 1.49/0.58  % (23980)Time elapsed: 0.152 s
% 1.49/0.58  % (23980)------------------------------
% 1.49/0.58  % (23980)------------------------------
% 1.49/0.58  % (23985)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.49/0.58  % (23988)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.49/0.58  % (23970)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.49/0.58  % SZS output start Proof for theBenchmark
% 1.49/0.58  fof(f130,plain,(
% 1.49/0.58    $false),
% 1.49/0.58    inference(subsumption_resolution,[],[f129,f77])).
% 1.49/0.58  fof(f77,plain,(
% 1.49/0.58    k1_xboole_0 != sK1),
% 1.49/0.58    inference(subsumption_resolution,[],[f76,f69])).
% 1.49/0.58  fof(f69,plain,(
% 1.49/0.58    ( ! [X3] : (v1_relat_1(k1_xboole_0) | k1_xboole_0 != X3) )),
% 1.49/0.58    inference(superposition,[],[f30,f65])).
% 1.49/0.58  fof(f65,plain,(
% 1.49/0.58    ( ! [X0] : (k1_xboole_0 = sK3(X0) | k1_xboole_0 != X0) )),
% 1.49/0.58    inference(superposition,[],[f53,f32])).
% 1.49/0.58  fof(f32,plain,(
% 1.49/0.58    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 1.49/0.58    inference(cnf_transformation,[],[f16])).
% 1.49/0.58  fof(f16,plain,(
% 1.49/0.58    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.49/0.58    inference(ennf_transformation,[],[f7])).
% 1.49/0.58  fof(f7,axiom,(
% 1.49/0.58    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.49/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 1.49/0.58  fof(f53,plain,(
% 1.49/0.58    ( ! [X0] : (k1_xboole_0 != k1_relat_1(sK3(X0)) | k1_xboole_0 = sK3(X0)) )),
% 1.49/0.58    inference(resolution,[],[f23,f30])).
% 1.49/0.58  fof(f23,plain,(
% 1.49/0.58    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.49/0.58    inference(cnf_transformation,[],[f14])).
% 1.49/0.58  fof(f14,plain,(
% 1.49/0.58    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.49/0.58    inference(flattening,[],[f13])).
% 1.49/0.58  fof(f13,plain,(
% 1.49/0.58    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.49/0.58    inference(ennf_transformation,[],[f6])).
% 1.49/0.58  fof(f6,axiom,(
% 1.49/0.58    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.49/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.49/0.58  fof(f30,plain,(
% 1.49/0.58    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 1.49/0.58    inference(cnf_transformation,[],[f16])).
% 1.49/0.58  fof(f76,plain,(
% 1.49/0.58    k1_xboole_0 != sK1 | ~v1_relat_1(k1_xboole_0)),
% 1.49/0.58    inference(subsumption_resolution,[],[f75,f68])).
% 1.49/0.58  fof(f68,plain,(
% 1.49/0.58    ( ! [X2] : (v1_funct_1(k1_xboole_0) | k1_xboole_0 != X2) )),
% 1.49/0.58    inference(superposition,[],[f31,f65])).
% 1.49/0.58  fof(f31,plain,(
% 1.49/0.58    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 1.49/0.58    inference(cnf_transformation,[],[f16])).
% 1.49/0.58  fof(f75,plain,(
% 1.49/0.58    k1_xboole_0 != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.49/0.58    inference(forward_demodulation,[],[f74,f20])).
% 1.49/0.58  fof(f20,plain,(
% 1.49/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.49/0.58    inference(cnf_transformation,[],[f5])).
% 1.49/0.58  fof(f5,axiom,(
% 1.49/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.49/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.49/0.58  fof(f74,plain,(
% 1.49/0.58    ~v1_funct_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) != sK1 | ~v1_relat_1(k1_xboole_0)),
% 1.49/0.58    inference(subsumption_resolution,[],[f73,f22])).
% 1.49/0.58  fof(f22,plain,(
% 1.49/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f3])).
% 1.49/0.58  fof(f3,axiom,(
% 1.49/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.49/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.49/0.58  fof(f73,plain,(
% 1.49/0.58    ~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | k1_relat_1(k1_xboole_0) != sK1 | ~v1_relat_1(k1_xboole_0)),
% 1.49/0.58    inference(superposition,[],[f18,f21])).
% 1.49/0.58  fof(f21,plain,(
% 1.49/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.49/0.58    inference(cnf_transformation,[],[f5])).
% 1.49/0.58  fof(f18,plain,(
% 1.49/0.58    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK1 | ~v1_relat_1(X2)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f12])).
% 1.49/0.58  fof(f12,plain,(
% 1.49/0.58    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.49/0.58    inference(flattening,[],[f11])).
% 1.49/0.58  fof(f11,plain,(
% 1.49/0.58    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.49/0.58    inference(ennf_transformation,[],[f10])).
% 1.49/0.58  fof(f10,negated_conjecture,(
% 1.49/0.58    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.49/0.58    inference(negated_conjecture,[],[f9])).
% 1.49/0.58  fof(f9,conjecture,(
% 1.49/0.58    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.49/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 1.49/0.58  fof(f129,plain,(
% 1.49/0.58    k1_xboole_0 = sK1),
% 1.49/0.58    inference(equality_resolution,[],[f128])).
% 1.49/0.58  fof(f128,plain,(
% 1.49/0.58    ( ! [X5] : (sK1 != X5 | k1_xboole_0 = X5) )),
% 1.49/0.58    inference(global_subsumption,[],[f19,f77,f127])).
% 1.49/0.58  fof(f127,plain,(
% 1.49/0.58    ( ! [X5] : (sK1 != X5 | k1_xboole_0 = X5 | k1_xboole_0 = sK0) )),
% 1.49/0.58    inference(resolution,[],[f124,f58])).
% 1.49/0.58  fof(f58,plain,(
% 1.49/0.58    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.49/0.58    inference(resolution,[],[f35,f22])).
% 1.49/0.58  fof(f35,plain,(
% 1.49/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.49/0.58    inference(cnf_transformation,[],[f2])).
% 1.49/0.58  fof(f2,axiom,(
% 1.49/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.49/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.49/0.58  fof(f124,plain,(
% 1.49/0.58    ( ! [X0,X1] : (r1_tarski(sK0,X1) | sK1 != X0 | k1_xboole_0 = X0) )),
% 1.49/0.58    inference(duplicate_literal_removal,[],[f123])).
% 1.49/0.58  fof(f123,plain,(
% 1.49/0.58    ( ! [X0,X1] : (sK1 != X0 | r1_tarski(sK0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 1.49/0.58    inference(superposition,[],[f119,f27])).
% 1.49/0.58  fof(f27,plain,(
% 1.49/0.58    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.49/0.58    inference(cnf_transformation,[],[f15])).
% 1.49/0.58  fof(f15,plain,(
% 1.49/0.58    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.49/0.58    inference(ennf_transformation,[],[f8])).
% 1.49/0.58  fof(f8,axiom,(
% 1.49/0.58    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.49/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 1.49/0.58  fof(f119,plain,(
% 1.49/0.58    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X1,sK4(sK0,X0))) | r1_tarski(sK0,X0) | k1_xboole_0 = X1) )),
% 1.49/0.58    inference(resolution,[],[f118,f81])).
% 1.49/0.58  fof(f81,plain,(
% 1.49/0.58    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | sK1 != k1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.49/0.58    inference(subsumption_resolution,[],[f80,f25])).
% 1.49/0.58  fof(f25,plain,(
% 1.49/0.58    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.49/0.58    inference(cnf_transformation,[],[f15])).
% 1.49/0.58  fof(f80,plain,(
% 1.49/0.58    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | sK1 != k1_relat_1(sK2(X0,X1)) | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.49/0.58    inference(subsumption_resolution,[],[f78,f26])).
% 1.49/0.58  fof(f26,plain,(
% 1.49/0.58    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.49/0.58    inference(cnf_transformation,[],[f15])).
% 1.49/0.58  fof(f78,plain,(
% 1.49/0.58    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),sK0) | ~v1_funct_1(sK2(X0,X1)) | sK1 != k1_relat_1(sK2(X0,X1)) | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.49/0.58    inference(superposition,[],[f18,f28])).
% 1.49/0.58  fof(f28,plain,(
% 1.49/0.58    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.49/0.58    inference(cnf_transformation,[],[f15])).
% 1.49/0.58  fof(f118,plain,(
% 1.49/0.58    ( ! [X1] : (r1_tarski(k1_tarski(sK4(sK0,X1)),sK0) | r1_tarski(sK0,X1)) )),
% 1.49/0.58    inference(resolution,[],[f115,f37])).
% 1.49/0.58  fof(f37,plain,(
% 1.49/0.58    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f17])).
% 1.49/0.58  fof(f17,plain,(
% 1.49/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.49/0.58    inference(ennf_transformation,[],[f1])).
% 1.49/0.58  fof(f1,axiom,(
% 1.49/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.49/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.49/0.58  fof(f115,plain,(
% 1.49/0.58    ( ! [X0] : (~r2_hidden(X0,sK0) | r1_tarski(k1_tarski(X0),sK0)) )),
% 1.49/0.58    inference(superposition,[],[f38,f113])).
% 1.49/0.58  fof(f113,plain,(
% 1.49/0.58    ( ! [X0] : (sK4(k1_tarski(X0),sK0) = X0) )),
% 1.49/0.58    inference(subsumption_resolution,[],[f112,f77])).
% 1.49/0.58  fof(f112,plain,(
% 1.49/0.58    ( ! [X0] : (sK4(k1_tarski(X0),sK0) = X0 | k1_xboole_0 = sK1) )),
% 1.49/0.58    inference(equality_resolution,[],[f111])).
% 1.49/0.58  fof(f111,plain,(
% 1.49/0.58    ( ! [X0,X1] : (sK1 != X0 | sK4(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0) )),
% 1.49/0.58    inference(duplicate_literal_removal,[],[f110])).
% 1.49/0.58  fof(f110,plain,(
% 1.49/0.58    ( ! [X0,X1] : (sK1 != X0 | sK4(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 1.49/0.58    inference(superposition,[],[f84,f27])).
% 1.49/0.58  fof(f84,plain,(
% 1.49/0.58    ( ! [X2,X3] : (sK1 != k1_relat_1(sK2(X3,X2)) | sK4(k1_tarski(X2),sK0) = X2 | k1_xboole_0 = X3) )),
% 1.49/0.58    inference(resolution,[],[f50,f81])).
% 1.49/0.58  fof(f50,plain,(
% 1.49/0.58    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | sK4(k1_tarski(X0),X1) = X0) )),
% 1.49/0.58    inference(resolution,[],[f37,f45])).
% 1.49/0.58  fof(f45,plain,(
% 1.49/0.58    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.49/0.58    inference(equality_resolution,[],[f40])).
% 1.49/0.58  fof(f40,plain,(
% 1.49/0.58    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.49/0.58    inference(cnf_transformation,[],[f4])).
% 1.49/0.58  fof(f4,axiom,(
% 1.49/0.58    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.49/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.49/0.58  fof(f38,plain,(
% 1.49/0.58    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.49/0.58    inference(cnf_transformation,[],[f17])).
% 1.49/0.58  fof(f19,plain,(
% 1.49/0.58    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.49/0.58    inference(cnf_transformation,[],[f12])).
% 1.49/0.58  % SZS output end Proof for theBenchmark
% 1.49/0.58  % (23969)------------------------------
% 1.49/0.58  % (23969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.58  % (23969)Termination reason: Refutation
% 1.49/0.58  
% 1.49/0.58  % (23969)Memory used [KB]: 6268
% 1.49/0.58  % (23969)Time elapsed: 0.141 s
% 1.49/0.58  % (23969)------------------------------
% 1.49/0.58  % (23969)------------------------------
% 1.49/0.59  % (23963)Refutation not found, incomplete strategy% (23963)------------------------------
% 1.49/0.59  % (23963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.59  % (23963)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.59  
% 1.49/0.59  % (23963)Memory used [KB]: 1663
% 1.49/0.59  % (23963)Time elapsed: 0.145 s
% 1.49/0.59  % (23963)------------------------------
% 1.49/0.59  % (23963)------------------------------
% 1.49/0.59  % (23962)Success in time 0.218 s
%------------------------------------------------------------------------------
