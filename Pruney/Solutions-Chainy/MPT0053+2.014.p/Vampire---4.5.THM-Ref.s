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
% DateTime   : Thu Dec  3 12:29:58 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 279 expanded)
%              Number of leaves         :    5 (  77 expanded)
%              Depth                    :   20
%              Number of atoms          :   84 ( 642 expanded)
%              Number of equality atoms :   38 ( 248 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f272])).

% (7079)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f272,plain,(
    o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(superposition,[],[f23,f270])).

fof(f270,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(subsumption_resolution,[],[f269,f144])).

% (7076)Refutation not found, incomplete strategy% (7076)------------------------------
% (7076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7076)Termination reason: Refutation not found, incomplete strategy

% (7076)Memory used [KB]: 10618
% (7076)Time elapsed: 0.128 s
% (7076)------------------------------
% (7076)------------------------------
fof(f144,plain,(
    ! [X1] : ~ r2_hidden(X1,o_0_0_xboole_0) ),
    inference(subsumption_resolution,[],[f142,f69])).

fof(f69,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,o_0_0_xboole_0)
      | ~ r2_hidden(X3,X2) ) ),
    inference(superposition,[],[f26,f67])).

fof(f67,plain,(
    ! [X2] : o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X2) ),
    inference(subsumption_resolution,[],[f62,f60])).

% (7079)Refutation not found, incomplete strategy% (7079)------------------------------
% (7079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7079)Termination reason: Refutation not found, incomplete strategy

% (7079)Memory used [KB]: 6140
% (7079)Time elapsed: 0.137 s
% (7079)------------------------------
% (7079)------------------------------
fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(o_0_0_xboole_0,X1,o_0_0_xboole_0),X0)
      | o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X1) ) ),
    inference(superposition,[],[f49,f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f10,f9])).

fof(f9,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f10,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f49,plain,(
    ! [X14,X12,X13] :
      ( r2_hidden(sK2(X12,X13,X12),k2_xboole_0(X14,X12))
      | k4_xboole_0(X12,X13) = X12 ) ),
    inference(resolution,[],[f44,f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f62,plain,(
    ! [X2,X3] :
      ( o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X2)
      | ~ r2_hidden(sK2(o_0_0_xboole_0,X2,o_0_0_xboole_0),X3) ) ),
    inference(resolution,[],[f60,f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,o_0_0_xboole_0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f27,f134])).

fof(f134,plain,(
    ! [X1] : o_0_0_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(subsumption_resolution,[],[f132,f111])).

fof(f111,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK2(X10,X10,o_0_0_xboole_0),X11)
      | o_0_0_xboole_0 = k4_xboole_0(X10,X10) ) ),
    inference(resolution,[],[f106,f69])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X0,X1),X1)
      | k4_xboole_0(X0,X0) = X1 ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X0,X1),X1)
      | k4_xboole_0(X0,X0) = X1
      | r2_hidden(sK2(X0,X0,X1),X1)
      | k4_xboole_0(X0,X0) = X1 ) ),
    inference(resolution,[],[f13,f12])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f132,plain,(
    ! [X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(X1,X1)
      | r2_hidden(sK2(X1,X1,o_0_0_xboole_0),X1) ) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,(
    ! [X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(X1,X1)
      | r2_hidden(sK2(X1,X1,o_0_0_xboole_0),X1)
      | o_0_0_xboole_0 = k4_xboole_0(X1,X1) ) ),
    inference(resolution,[],[f111,f12])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f269,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))
      | r2_hidden(sK2(X0,k2_xboole_0(X0,X1),o_0_0_xboole_0),o_0_0_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f263])).

fof(f263,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))
      | r2_hidden(sK2(X0,k2_xboole_0(X0,X1),o_0_0_xboole_0),o_0_0_xboole_0)
      | o_0_0_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f181,f13])).

fof(f181,plain,(
    ! [X6,X4,X5] :
      ( r2_hidden(sK2(X4,X5,o_0_0_xboole_0),k2_xboole_0(X4,X6))
      | o_0_0_xboole_0 = k4_xboole_0(X4,X5) ) ),
    inference(resolution,[],[f146,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

% (7066)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f146,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK2(X2,X3,o_0_0_xboole_0),X2)
      | o_0_0_xboole_0 = k4_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f144,f12])).

fof(f23,plain,(
    o_0_0_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f8,f9])).

fof(f8,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 16:54:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.24/0.53  % (7064)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.24/0.54  % (7064)Refutation not found, incomplete strategy% (7064)------------------------------
% 1.24/0.54  % (7064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (7064)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (7064)Memory used [KB]: 10618
% 1.24/0.54  % (7064)Time elapsed: 0.105 s
% 1.24/0.54  % (7064)------------------------------
% 1.24/0.54  % (7064)------------------------------
% 1.24/0.54  % (7068)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.24/0.54  % (7060)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.24/0.54  % (7080)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.24/0.55  % (7062)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.24/0.55  % (7060)Refutation found. Thanks to Tanya!
% 1.24/0.55  % SZS status Theorem for theBenchmark
% 1.24/0.55  % (7069)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.24/0.55  % (7069)Refutation not found, incomplete strategy% (7069)------------------------------
% 1.24/0.55  % (7069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.55  % (7069)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.55  
% 1.24/0.55  % (7069)Memory used [KB]: 6140
% 1.24/0.55  % (7069)Time elapsed: 0.001 s
% 1.24/0.55  % (7069)------------------------------
% 1.24/0.55  % (7069)------------------------------
% 1.24/0.55  % (7072)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.24/0.55  % (7055)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.24/0.55  % (7056)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.55  % (7056)Refutation not found, incomplete strategy% (7056)------------------------------
% 1.24/0.55  % (7056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.55  % (7056)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.55  
% 1.24/0.55  % (7056)Memory used [KB]: 10618
% 1.24/0.55  % (7056)Time elapsed: 0.133 s
% 1.24/0.55  % (7056)------------------------------
% 1.24/0.55  % (7056)------------------------------
% 1.24/0.55  % (7075)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.24/0.55  % (7075)Refutation not found, incomplete strategy% (7075)------------------------------
% 1.24/0.55  % (7075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.55  % (7075)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.55  
% 1.24/0.55  % (7075)Memory used [KB]: 1663
% 1.24/0.55  % (7075)Time elapsed: 0.134 s
% 1.24/0.55  % (7075)------------------------------
% 1.24/0.55  % (7075)------------------------------
% 1.24/0.56  % (7077)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.24/0.56  % (7081)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.24/0.56  % (7076)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.24/0.56  % (7074)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.24/0.56  % (7083)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.24/0.56  % SZS output start Proof for theBenchmark
% 1.24/0.56  fof(f279,plain,(
% 1.24/0.56    $false),
% 1.24/0.56    inference(trivial_inequality_removal,[],[f272])).
% 1.24/0.56  % (7079)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.24/0.56  fof(f272,plain,(
% 1.24/0.56    o_0_0_xboole_0 != o_0_0_xboole_0),
% 1.24/0.56    inference(superposition,[],[f23,f270])).
% 1.24/0.56  fof(f270,plain,(
% 1.24/0.56    ( ! [X0,X1] : (o_0_0_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.24/0.56    inference(subsumption_resolution,[],[f269,f144])).
% 1.24/0.56  % (7076)Refutation not found, incomplete strategy% (7076)------------------------------
% 1.24/0.56  % (7076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.56  % (7076)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.56  
% 1.24/0.56  % (7076)Memory used [KB]: 10618
% 1.24/0.56  % (7076)Time elapsed: 0.128 s
% 1.24/0.56  % (7076)------------------------------
% 1.24/0.56  % (7076)------------------------------
% 1.24/0.56  fof(f144,plain,(
% 1.24/0.56    ( ! [X1] : (~r2_hidden(X1,o_0_0_xboole_0)) )),
% 1.24/0.56    inference(subsumption_resolution,[],[f142,f69])).
% 1.24/0.56  fof(f69,plain,(
% 1.24/0.56    ( ! [X2,X3] : (~r2_hidden(X3,o_0_0_xboole_0) | ~r2_hidden(X3,X2)) )),
% 1.24/0.56    inference(superposition,[],[f26,f67])).
% 1.24/0.56  fof(f67,plain,(
% 1.24/0.56    ( ! [X2] : (o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X2)) )),
% 1.24/0.56    inference(subsumption_resolution,[],[f62,f60])).
% 1.24/0.56  % (7079)Refutation not found, incomplete strategy% (7079)------------------------------
% 1.24/0.56  % (7079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.56  % (7079)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.56  
% 1.24/0.56  % (7079)Memory used [KB]: 6140
% 1.24/0.56  % (7079)Time elapsed: 0.137 s
% 1.24/0.56  % (7079)------------------------------
% 1.24/0.56  % (7079)------------------------------
% 1.24/0.56  fof(f60,plain,(
% 1.24/0.56    ( ! [X0,X1] : (r2_hidden(sK2(o_0_0_xboole_0,X1,o_0_0_xboole_0),X0) | o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X1)) )),
% 1.24/0.56    inference(superposition,[],[f49,f24])).
% 1.24/0.56  fof(f24,plain,(
% 1.24/0.56    ( ! [X0] : (k2_xboole_0(X0,o_0_0_xboole_0) = X0) )),
% 1.24/0.56    inference(definition_unfolding,[],[f10,f9])).
% 1.24/0.56  fof(f9,plain,(
% 1.24/0.56    k1_xboole_0 = o_0_0_xboole_0),
% 1.24/0.56    inference(cnf_transformation,[],[f1])).
% 1.24/0.56  fof(f1,axiom,(
% 1.24/0.56    k1_xboole_0 = o_0_0_xboole_0),
% 1.24/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).
% 1.24/0.56  fof(f10,plain,(
% 1.24/0.56    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.24/0.56    inference(cnf_transformation,[],[f4])).
% 1.24/0.56  fof(f4,axiom,(
% 1.24/0.56    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.24/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.24/0.56  fof(f49,plain,(
% 1.24/0.56    ( ! [X14,X12,X13] : (r2_hidden(sK2(X12,X13,X12),k2_xboole_0(X14,X12)) | k4_xboole_0(X12,X13) = X12) )),
% 1.24/0.56    inference(resolution,[],[f44,f28])).
% 1.24/0.56  fof(f28,plain,(
% 1.24/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 1.24/0.56    inference(equality_resolution,[],[f22])).
% 1.24/0.56  fof(f22,plain,(
% 1.24/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.24/0.56    inference(cnf_transformation,[],[f2])).
% 1.24/0.56  fof(f2,axiom,(
% 1.24/0.56    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.24/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.24/0.56  fof(f44,plain,(
% 1.24/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 1.24/0.56    inference(factoring,[],[f12])).
% 1.24/0.56  fof(f12,plain,(
% 1.24/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.24/0.56    inference(cnf_transformation,[],[f3])).
% 1.24/0.56  fof(f3,axiom,(
% 1.24/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.24/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.24/0.56  fof(f62,plain,(
% 1.24/0.56    ( ! [X2,X3] : (o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X2) | ~r2_hidden(sK2(o_0_0_xboole_0,X2,o_0_0_xboole_0),X3)) )),
% 1.24/0.56    inference(resolution,[],[f60,f26])).
% 1.24/0.56  fof(f26,plain,(
% 1.24/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 1.24/0.56    inference(equality_resolution,[],[f15])).
% 1.24/0.56  fof(f15,plain,(
% 1.24/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.24/0.56    inference(cnf_transformation,[],[f3])).
% 1.24/0.56  fof(f142,plain,(
% 1.24/0.56    ( ! [X0,X1] : (~r2_hidden(X1,o_0_0_xboole_0) | r2_hidden(X1,X0)) )),
% 1.24/0.56    inference(superposition,[],[f27,f134])).
% 1.24/0.56  fof(f134,plain,(
% 1.24/0.56    ( ! [X1] : (o_0_0_xboole_0 = k4_xboole_0(X1,X1)) )),
% 1.24/0.56    inference(subsumption_resolution,[],[f132,f111])).
% 1.24/0.56  fof(f111,plain,(
% 1.24/0.56    ( ! [X10,X11] : (~r2_hidden(sK2(X10,X10,o_0_0_xboole_0),X11) | o_0_0_xboole_0 = k4_xboole_0(X10,X10)) )),
% 1.24/0.56    inference(resolution,[],[f106,f69])).
% 1.24/0.56  fof(f106,plain,(
% 1.24/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X0,X1),X1) | k4_xboole_0(X0,X0) = X1) )),
% 1.24/0.56    inference(duplicate_literal_removal,[],[f91])).
% 1.24/0.56  fof(f91,plain,(
% 1.24/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X0,X1),X1) | k4_xboole_0(X0,X0) = X1 | r2_hidden(sK2(X0,X0,X1),X1) | k4_xboole_0(X0,X0) = X1) )),
% 1.24/0.56    inference(resolution,[],[f13,f12])).
% 1.24/0.56  fof(f13,plain,(
% 1.24/0.56    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.24/0.56    inference(cnf_transformation,[],[f3])).
% 1.24/0.56  fof(f132,plain,(
% 1.24/0.56    ( ! [X1] : (o_0_0_xboole_0 = k4_xboole_0(X1,X1) | r2_hidden(sK2(X1,X1,o_0_0_xboole_0),X1)) )),
% 1.24/0.56    inference(duplicate_literal_removal,[],[f117])).
% 1.24/0.56  fof(f117,plain,(
% 1.24/0.56    ( ! [X1] : (o_0_0_xboole_0 = k4_xboole_0(X1,X1) | r2_hidden(sK2(X1,X1,o_0_0_xboole_0),X1) | o_0_0_xboole_0 = k4_xboole_0(X1,X1)) )),
% 1.24/0.56    inference(resolution,[],[f111,f12])).
% 1.24/0.56  fof(f27,plain,(
% 1.24/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 1.24/0.56    inference(equality_resolution,[],[f14])).
% 1.24/0.56  fof(f14,plain,(
% 1.24/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.24/0.56    inference(cnf_transformation,[],[f3])).
% 1.24/0.56  fof(f269,plain,(
% 1.24/0.56    ( ! [X0,X1] : (o_0_0_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) | r2_hidden(sK2(X0,k2_xboole_0(X0,X1),o_0_0_xboole_0),o_0_0_xboole_0)) )),
% 1.24/0.56    inference(duplicate_literal_removal,[],[f263])).
% 1.24/0.56  fof(f263,plain,(
% 1.24/0.56    ( ! [X0,X1] : (o_0_0_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) | r2_hidden(sK2(X0,k2_xboole_0(X0,X1),o_0_0_xboole_0),o_0_0_xboole_0) | o_0_0_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.24/0.56    inference(resolution,[],[f181,f13])).
% 1.24/0.56  fof(f181,plain,(
% 1.24/0.56    ( ! [X6,X4,X5] : (r2_hidden(sK2(X4,X5,o_0_0_xboole_0),k2_xboole_0(X4,X6)) | o_0_0_xboole_0 = k4_xboole_0(X4,X5)) )),
% 1.24/0.56    inference(resolution,[],[f146,f29])).
% 1.24/0.56  fof(f29,plain,(
% 1.24/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 1.24/0.56    inference(equality_resolution,[],[f21])).
% 1.24/0.56  fof(f21,plain,(
% 1.24/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.24/0.56    inference(cnf_transformation,[],[f2])).
% 1.24/0.56  % (7066)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.24/0.56  fof(f146,plain,(
% 1.24/0.56    ( ! [X2,X3] : (r2_hidden(sK2(X2,X3,o_0_0_xboole_0),X2) | o_0_0_xboole_0 = k4_xboole_0(X2,X3)) )),
% 1.24/0.56    inference(resolution,[],[f144,f12])).
% 1.24/0.56  fof(f23,plain,(
% 1.24/0.56    o_0_0_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 1.24/0.56    inference(definition_unfolding,[],[f8,f9])).
% 1.24/0.56  fof(f8,plain,(
% 1.24/0.56    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 1.24/0.56    inference(cnf_transformation,[],[f7])).
% 1.24/0.56  fof(f7,plain,(
% 1.24/0.56    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.24/0.56    inference(ennf_transformation,[],[f6])).
% 1.24/0.56  fof(f6,negated_conjecture,(
% 1.24/0.56    ~! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.24/0.56    inference(negated_conjecture,[],[f5])).
% 1.24/0.56  fof(f5,conjecture,(
% 1.24/0.56    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.24/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.24/0.56  % SZS output end Proof for theBenchmark
% 1.24/0.56  % (7060)------------------------------
% 1.24/0.56  % (7060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.56  % (7060)Termination reason: Refutation
% 1.24/0.56  
% 1.24/0.56  % (7060)Memory used [KB]: 6396
% 1.24/0.56  % (7060)Time elapsed: 0.124 s
% 1.24/0.56  % (7060)------------------------------
% 1.24/0.56  % (7060)------------------------------
% 1.24/0.56  % (7053)Success in time 0.185 s
%------------------------------------------------------------------------------
