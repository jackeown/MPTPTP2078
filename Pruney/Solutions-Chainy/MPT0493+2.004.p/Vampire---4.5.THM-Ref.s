%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  59 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 136 expanded)
%              Number of equality atoms :   35 (  53 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f663,plain,(
    $false ),
    inference(subsumption_resolution,[],[f657,f17])).

fof(f17,plain,(
    sK0 != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f657,plain,(
    sK0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f645,f82])).

fof(f82,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))) ),
    inference(superposition,[],[f81,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f81,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f31,f15])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f645,plain,(
    sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) ),
    inference(superposition,[],[f628,f30])).

% (12130)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

% (12137)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f628,plain,(
    ! [X6] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X6,k1_relat_1(sK1))) ),
    inference(duplicate_literal_removal,[],[f613])).

fof(f613,plain,(
    ! [X6] :
      ( sK0 = k4_xboole_0(sK0,k4_xboole_0(X6,k1_relat_1(sK1)))
      | sK0 = k4_xboole_0(sK0,k4_xboole_0(X6,k1_relat_1(sK1))) ) ),
    inference(resolution,[],[f607,f435])).

fof(f435,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK2(sK0,X4,sK0),k4_xboole_0(X5,k1_relat_1(sK1)))
      | sK0 = k4_xboole_0(sK0,X4) ) ),
    inference(resolution,[],[f432,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f432,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK0,X0,sK0),k1_relat_1(sK1))
      | sK0 = k4_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f256,f16])).

fof(f16,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f256,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,X5)
      | k4_xboole_0(X3,X4) = X3
      | r2_hidden(sK2(X3,X4,X3),X5) ) ),
    inference(resolution,[],[f254,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f254,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f607,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK2(X5,X6,X5),X6)
      | k4_xboole_0(X5,X6) = X5 ) ),
    inference(subsumption_resolution,[],[f605,f254])).

fof(f605,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK2(X5,X6,X5),X6)
      | ~ r2_hidden(sK2(X5,X6,X5),X5)
      | k4_xboole_0(X5,X6) = X5 ) ),
    inference(duplicate_literal_removal,[],[f603])).

fof(f603,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK2(X5,X6,X5),X6)
      | ~ r2_hidden(sK2(X5,X6,X5),X5)
      | k4_xboole_0(X5,X6) = X5
      | k4_xboole_0(X5,X6) = X5 ) ),
    inference(resolution,[],[f24,f254])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (12119)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.47  % (12119)Refutation not found, incomplete strategy% (12119)------------------------------
% 0.21/0.47  % (12119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (12119)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (12119)Memory used [KB]: 10618
% 0.21/0.47  % (12119)Time elapsed: 0.087 s
% 0.21/0.47  % (12119)------------------------------
% 0.21/0.47  % (12119)------------------------------
% 0.21/0.49  % (12126)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.49  % (12141)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.49  % (12133)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.50  % (12139)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (12131)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (12139)Refutation not found, incomplete strategy% (12139)------------------------------
% 0.21/0.50  % (12139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12139)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12139)Memory used [KB]: 10618
% 0.21/0.50  % (12139)Time elapsed: 0.058 s
% 0.21/0.50  % (12139)------------------------------
% 0.21/0.50  % (12139)------------------------------
% 0.21/0.50  % (12123)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (12122)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (12121)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (12128)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (12145)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (12129)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (12118)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (12120)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (12144)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (12146)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (12117)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (12132)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (12124)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (12136)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (12127)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (12140)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (12138)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (12127)Refutation not found, incomplete strategy% (12127)------------------------------
% 0.21/0.54  % (12127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12127)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12127)Memory used [KB]: 10618
% 0.21/0.54  % (12127)Time elapsed: 0.133 s
% 0.21/0.54  % (12127)------------------------------
% 0.21/0.54  % (12127)------------------------------
% 0.21/0.54  % (12138)Refutation not found, incomplete strategy% (12138)------------------------------
% 0.21/0.54  % (12138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12138)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12138)Memory used [KB]: 1663
% 0.21/0.54  % (12138)Time elapsed: 0.140 s
% 0.21/0.54  % (12138)------------------------------
% 0.21/0.54  % (12138)------------------------------
% 0.21/0.54  % (12123)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (12135)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f663,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f657,f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    sK0 != k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ? [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.54    inference(negated_conjecture,[],[f8])).
% 0.21/0.54  fof(f8,conjecture,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.54  fof(f657,plain,(
% 0.21/0.54    sK0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.54    inference(superposition,[],[f645,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))) )),
% 0.21/0.54    inference(superposition,[],[f81,f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) )),
% 0.21/0.54    inference(resolution,[],[f31,f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    v1_relat_1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f22,f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.54  fof(f645,plain,(
% 0.21/0.54    sK0 = k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1)))),
% 0.21/0.54    inference(superposition,[],[f628,f30])).
% 0.21/0.54  % (12130)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f21,f20])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.54  % (12137)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  fof(f628,plain,(
% 0.21/0.54    ( ! [X6] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X6,k1_relat_1(sK1)))) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f613])).
% 0.21/0.54  fof(f613,plain,(
% 0.21/0.54    ( ! [X6] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X6,k1_relat_1(sK1))) | sK0 = k4_xboole_0(sK0,k4_xboole_0(X6,k1_relat_1(sK1)))) )),
% 0.21/0.54    inference(resolution,[],[f607,f435])).
% 0.21/0.54  fof(f435,plain,(
% 0.21/0.54    ( ! [X4,X5] : (~r2_hidden(sK2(sK0,X4,sK0),k4_xboole_0(X5,k1_relat_1(sK1))) | sK0 = k4_xboole_0(sK0,X4)) )),
% 0.21/0.54    inference(resolution,[],[f432,f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(equality_resolution,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.55  fof(f432,plain,(
% 0.21/0.55    ( ! [X0] : (r2_hidden(sK2(sK0,X0,sK0),k1_relat_1(sK1)) | sK0 = k4_xboole_0(sK0,X0)) )),
% 0.21/0.55    inference(resolution,[],[f256,f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f256,plain,(
% 0.21/0.55    ( ! [X4,X5,X3] : (~r1_tarski(X3,X5) | k4_xboole_0(X3,X4) = X3 | r2_hidden(sK2(X3,X4,X3),X5)) )),
% 0.21/0.55    inference(resolution,[],[f254,f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r1_tarski(X0,X1) | r2_hidden(X2,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.55  fof(f254,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.55    inference(factoring,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f607,plain,(
% 0.21/0.55    ( ! [X6,X5] : (r2_hidden(sK2(X5,X6,X5),X6) | k4_xboole_0(X5,X6) = X5) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f605,f254])).
% 0.21/0.55  fof(f605,plain,(
% 0.21/0.55    ( ! [X6,X5] : (r2_hidden(sK2(X5,X6,X5),X6) | ~r2_hidden(sK2(X5,X6,X5),X5) | k4_xboole_0(X5,X6) = X5) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f603])).
% 0.21/0.55  fof(f603,plain,(
% 0.21/0.55    ( ! [X6,X5] : (r2_hidden(sK2(X5,X6,X5),X6) | ~r2_hidden(sK2(X5,X6,X5),X5) | k4_xboole_0(X5,X6) = X5 | k4_xboole_0(X5,X6) = X5) )),
% 0.21/0.55    inference(resolution,[],[f24,f254])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (12123)------------------------------
% 0.21/0.55  % (12123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (12123)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (12123)Memory used [KB]: 6780
% 0.21/0.55  % (12123)Time elapsed: 0.101 s
% 0.21/0.55  % (12123)------------------------------
% 0.21/0.55  % (12123)------------------------------
% 0.21/0.55  % (12137)Refutation not found, incomplete strategy% (12137)------------------------------
% 0.21/0.55  % (12137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (12137)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (12137)Memory used [KB]: 10746
% 0.21/0.55  % (12137)Time elapsed: 0.153 s
% 0.21/0.55  % (12137)------------------------------
% 0.21/0.55  % (12137)------------------------------
% 0.21/0.55  % (12116)Success in time 0.187 s
%------------------------------------------------------------------------------
