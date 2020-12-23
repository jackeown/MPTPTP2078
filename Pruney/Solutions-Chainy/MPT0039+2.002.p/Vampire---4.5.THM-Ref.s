%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 303 expanded)
%              Number of leaves         :    2 (  71 expanded)
%              Depth                    :   16
%              Number of atoms          :   97 ( 748 expanded)
%              Number of equality atoms :   38 ( 286 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1628,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1627,f8])).

fof(f8,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f1627,plain,(
    sK0 = sK1 ),
    inference(backward_demodulation,[],[f1467,f1622])).

fof(f1622,plain,(
    ! [X17] : sK0 = k4_xboole_0(sK1,k4_xboole_0(X17,X17)) ),
    inference(resolution,[],[f1597,f109])).

fof(f109,plain,(
    ! [X4,X3] : ~ r2_hidden(X4,k4_xboole_0(X3,X3)) ),
    inference(superposition,[],[f37,f99])).

fof(f99,plain,(
    ! [X0] : k4_xboole_0(sK0,sK1) = k4_xboole_0(X0,X0) ),
    inference(subsumption_resolution,[],[f98,f37])).

fof(f98,plain,(
    ! [X0] :
      ( k4_xboole_0(sK0,sK1) = k4_xboole_0(X0,X0)
      | r2_hidden(sK2(X0,X0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( k4_xboole_0(sK0,sK1) = k4_xboole_0(X0,X0)
      | r2_hidden(sK2(X0,X0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
      | k4_xboole_0(sK0,sK1) = k4_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f44,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
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

fof(f44,plain,(
    ! [X10,X9] :
      ( r2_hidden(sK2(X9,X10,k4_xboole_0(sK0,sK1)),X9)
      | k4_xboole_0(sK0,sK1) = k4_xboole_0(X9,X10) ) ),
    inference(resolution,[],[f37,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X3] : ~ r2_hidden(X3,k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f34,f23])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k4_xboole_0(sK0,sK1))
      | r2_hidden(X3,sK1) ) ),
    inference(superposition,[],[f24,f7])).

fof(f7,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f1597,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0,sK0),X0)
      | sK0 = k4_xboole_0(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f1595,f1558])).

fof(f1558,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0,sK0),sK0)
      | sK0 = k4_xboole_0(sK1,X0) ) ),
    inference(factoring,[],[f61])).

fof(f61,plain,(
    ! [X12,X13] :
      ( r2_hidden(sK2(sK1,X12,X13),sK0)
      | r2_hidden(sK2(sK1,X12,X13),X13)
      | k4_xboole_0(sK1,X12) = X13 ) ),
    inference(resolution,[],[f38,f11])).

fof(f38,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK1)
      | r2_hidden(X5,sK0) ) ),
    inference(subsumption_resolution,[],[f36,f37])).

fof(f36,plain,(
    ! [X5] :
      ( r2_hidden(X5,k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(X5,sK1)
      | r2_hidden(X5,sK0) ) ),
    inference(superposition,[],[f22,f7])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f1595,plain,(
    ! [X0] :
      ( sK0 = k4_xboole_0(sK1,X0)
      | r2_hidden(sK2(sK1,X0,sK0),X0)
      | ~ r2_hidden(sK2(sK1,X0,sK0),sK0) ) ),
    inference(duplicate_literal_removal,[],[f1589])).

fof(f1589,plain,(
    ! [X0] :
      ( sK0 = k4_xboole_0(sK1,X0)
      | r2_hidden(sK2(sK1,X0,sK0),X0)
      | ~ r2_hidden(sK2(sK1,X0,sK0),sK0)
      | sK0 = k4_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f1568,f10])).

fof(f10,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f1568,plain,(
    ! [X1] :
      ( r2_hidden(sK2(sK1,X1,sK0),sK1)
      | sK0 = k4_xboole_0(sK1,X1) ) ),
    inference(resolution,[],[f1558,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f37,f22])).

fof(f1467,plain,(
    ! [X18] : sK1 = k4_xboole_0(sK1,k4_xboole_0(X18,X18)) ),
    inference(resolution,[],[f1354,f109])).

fof(f1354,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0,sK1),X0)
      | sK1 = k4_xboole_0(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f1353,f1321])).

fof(f1321,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0,sK1),sK1)
      | sK1 = k4_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f1306,f39])).

fof(f1306,plain,(
    ! [X32] :
      ( r2_hidden(sK2(sK1,X32,sK1),sK0)
      | sK1 = k4_xboole_0(sK1,X32) ) ),
    inference(duplicate_literal_removal,[],[f1304])).

fof(f1304,plain,(
    ! [X32] :
      ( r2_hidden(sK2(sK1,X32,sK1),sK0)
      | sK1 = k4_xboole_0(sK1,X32)
      | r2_hidden(sK2(sK1,X32,sK1),sK0) ) ),
    inference(resolution,[],[f59,f38])).

fof(f59,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK2(X8,X9,sK1),sK0)
      | r2_hidden(sK2(X8,X9,sK1),X8)
      | sK1 = k4_xboole_0(X8,X9) ) ),
    inference(resolution,[],[f38,f11])).

fof(f1353,plain,(
    ! [X0] :
      ( sK1 = k4_xboole_0(sK1,X0)
      | r2_hidden(sK2(sK1,X0,sK1),X0)
      | ~ r2_hidden(sK2(sK1,X0,sK1),sK1) ) ),
    inference(duplicate_literal_removal,[],[f1345])).

fof(f1345,plain,(
    ! [X0] :
      ( sK1 = k4_xboole_0(sK1,X0)
      | r2_hidden(sK2(sK1,X0,sK1),X0)
      | ~ r2_hidden(sK2(sK1,X0,sK1),sK1)
      | sK1 = k4_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f1321,f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:37:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (396)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.47  % (407)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (398)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (399)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (404)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (404)Refutation not found, incomplete strategy% (404)------------------------------
% 0.22/0.49  % (404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (404)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (404)Memory used [KB]: 6012
% 0.22/0.49  % (404)Time elapsed: 0.003 s
% 0.22/0.49  % (404)------------------------------
% 0.22/0.49  % (404)------------------------------
% 0.22/0.49  % (401)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (408)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (412)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (397)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (392)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (393)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (411)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (400)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % (395)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (394)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (395)Refutation not found, incomplete strategy% (395)------------------------------
% 0.22/0.51  % (395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (395)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (395)Memory used [KB]: 10618
% 0.22/0.51  % (395)Time elapsed: 0.103 s
% 0.22/0.51  % (395)------------------------------
% 0.22/0.51  % (395)------------------------------
% 0.22/0.51  % (406)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (405)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (403)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (403)Refutation not found, incomplete strategy% (403)------------------------------
% 0.22/0.52  % (403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (403)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (403)Memory used [KB]: 10618
% 0.22/0.52  % (403)Time elapsed: 0.107 s
% 0.22/0.52  % (403)------------------------------
% 0.22/0.52  % (403)------------------------------
% 0.22/0.52  % (402)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (409)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.52  % (412)Refutation not found, incomplete strategy% (412)------------------------------
% 0.22/0.52  % (412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (412)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (412)Memory used [KB]: 10490
% 0.22/0.52  % (412)Time elapsed: 0.098 s
% 0.22/0.52  % (412)------------------------------
% 0.22/0.52  % (412)------------------------------
% 0.22/0.52  % (410)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.54  % (405)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f1628,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f1627,f8])).
% 0.22/0.54  fof(f8,plain,(
% 0.22/0.54    sK0 != sK1),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,plain,(
% 0.22/0.54    ? [X0,X1] : (X0 != X1 & k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 0.22/0.54    inference(negated_conjecture,[],[f4])).
% 0.22/0.54  fof(f4,conjecture,(
% 0.22/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).
% 0.22/0.54  fof(f1627,plain,(
% 0.22/0.54    sK0 = sK1),
% 0.22/0.54    inference(backward_demodulation,[],[f1467,f1622])).
% 0.22/0.54  fof(f1622,plain,(
% 0.22/0.54    ( ! [X17] : (sK0 = k4_xboole_0(sK1,k4_xboole_0(X17,X17))) )),
% 0.22/0.54    inference(resolution,[],[f1597,f109])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    ( ! [X4,X3] : (~r2_hidden(X4,k4_xboole_0(X3,X3))) )),
% 0.22/0.54    inference(superposition,[],[f37,f99])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ( ! [X0] : (k4_xboole_0(sK0,sK1) = k4_xboole_0(X0,X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f98,f37])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    ( ! [X0] : (k4_xboole_0(sK0,sK1) = k4_xboole_0(X0,X0) | r2_hidden(sK2(X0,X0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X0] : (k4_xboole_0(sK0,sK1) = k4_xboole_0(X0,X0) | r2_hidden(sK2(X0,X0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | k4_xboole_0(sK0,sK1) = k4_xboole_0(X0,X0)) )),
% 0.22/0.54    inference(resolution,[],[f44,f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X10,X9] : (r2_hidden(sK2(X9,X10,k4_xboole_0(sK0,sK1)),X9) | k4_xboole_0(sK0,sK1) = k4_xboole_0(X9,X10)) )),
% 0.22/0.54    inference(resolution,[],[f37,f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X3] : (~r2_hidden(X3,k4_xboole_0(sK0,sK1))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f34,f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X3] : (~r2_hidden(X3,k4_xboole_0(sK0,sK1)) | r2_hidden(X3,sK1)) )),
% 0.22/0.54    inference(superposition,[],[f24,f7])).
% 0.22/0.54  fof(f7,plain,(
% 0.22/0.54    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f1597,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK2(sK1,X0,sK0),X0) | sK0 = k4_xboole_0(sK1,X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f1595,f1558])).
% 0.22/0.54  fof(f1558,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK2(sK1,X0,sK0),sK0) | sK0 = k4_xboole_0(sK1,X0)) )),
% 0.22/0.54    inference(factoring,[],[f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X12,X13] : (r2_hidden(sK2(sK1,X12,X13),sK0) | r2_hidden(sK2(sK1,X12,X13),X13) | k4_xboole_0(sK1,X12) = X13) )),
% 0.22/0.54    inference(resolution,[],[f38,f11])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X5] : (~r2_hidden(X5,sK1) | r2_hidden(X5,sK0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f36,f37])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X5] : (r2_hidden(X5,k4_xboole_0(sK0,sK1)) | ~r2_hidden(X5,sK1) | r2_hidden(X5,sK0)) )),
% 0.22/0.54    inference(superposition,[],[f22,f7])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f1595,plain,(
% 0.22/0.54    ( ! [X0] : (sK0 = k4_xboole_0(sK1,X0) | r2_hidden(sK2(sK1,X0,sK0),X0) | ~r2_hidden(sK2(sK1,X0,sK0),sK0)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f1589])).
% 0.22/0.54  fof(f1589,plain,(
% 0.22/0.54    ( ! [X0] : (sK0 = k4_xboole_0(sK1,X0) | r2_hidden(sK2(sK1,X0,sK0),X0) | ~r2_hidden(sK2(sK1,X0,sK0),sK0) | sK0 = k4_xboole_0(sK1,X0)) )),
% 0.22/0.54    inference(resolution,[],[f1568,f10])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f1568,plain,(
% 0.22/0.54    ( ! [X1] : (r2_hidden(sK2(sK1,X1,sK0),sK1) | sK0 = k4_xboole_0(sK1,X1)) )),
% 0.22/0.54    inference(resolution,[],[f1558,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,sK1)) )),
% 0.22/0.54    inference(resolution,[],[f37,f22])).
% 0.22/0.54  fof(f1467,plain,(
% 0.22/0.54    ( ! [X18] : (sK1 = k4_xboole_0(sK1,k4_xboole_0(X18,X18))) )),
% 0.22/0.54    inference(resolution,[],[f1354,f109])).
% 0.22/0.54  fof(f1354,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK2(sK1,X0,sK1),X0) | sK1 = k4_xboole_0(sK1,X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f1353,f1321])).
% 0.22/0.54  fof(f1321,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK2(sK1,X0,sK1),sK1) | sK1 = k4_xboole_0(sK1,X0)) )),
% 0.22/0.54    inference(resolution,[],[f1306,f39])).
% 0.22/0.54  fof(f1306,plain,(
% 0.22/0.54    ( ! [X32] : (r2_hidden(sK2(sK1,X32,sK1),sK0) | sK1 = k4_xboole_0(sK1,X32)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f1304])).
% 0.22/0.54  fof(f1304,plain,(
% 0.22/0.54    ( ! [X32] : (r2_hidden(sK2(sK1,X32,sK1),sK0) | sK1 = k4_xboole_0(sK1,X32) | r2_hidden(sK2(sK1,X32,sK1),sK0)) )),
% 0.22/0.54    inference(resolution,[],[f59,f38])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X8,X9] : (r2_hidden(sK2(X8,X9,sK1),sK0) | r2_hidden(sK2(X8,X9,sK1),X8) | sK1 = k4_xboole_0(X8,X9)) )),
% 0.22/0.54    inference(resolution,[],[f38,f11])).
% 0.22/0.54  fof(f1353,plain,(
% 0.22/0.54    ( ! [X0] : (sK1 = k4_xboole_0(sK1,X0) | r2_hidden(sK2(sK1,X0,sK1),X0) | ~r2_hidden(sK2(sK1,X0,sK1),sK1)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f1345])).
% 0.22/0.54  fof(f1345,plain,(
% 0.22/0.54    ( ! [X0] : (sK1 = k4_xboole_0(sK1,X0) | r2_hidden(sK2(sK1,X0,sK1),X0) | ~r2_hidden(sK2(sK1,X0,sK1),sK1) | sK1 = k4_xboole_0(sK1,X0)) )),
% 0.22/0.54    inference(resolution,[],[f1321,f10])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (405)------------------------------
% 0.22/0.54  % (405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (405)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (405)Memory used [KB]: 2558
% 0.22/0.54  % (405)Time elapsed: 0.126 s
% 0.22/0.54  % (405)------------------------------
% 0.22/0.54  % (405)------------------------------
% 0.22/0.55  % (391)Success in time 0.184 s
%------------------------------------------------------------------------------
