%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:19 EST 2020

% Result     : CounterSatisfiable 1.22s
% Output     : Saturation 1.22s
% Verified   : 
% Statistics : Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    0
%              Number of atoms          :   20 (  20 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u22,axiom,
    ( r1_xboole_0(X0,k1_xboole_0) )).

cnf(u27,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )).

cnf(u33,axiom,
    ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X0,X2) )).

cnf(u28,axiom,
    ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) )).

cnf(u25,axiom,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 )).

cnf(u31,axiom,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    | r2_hidden(X0,X2) )).

cnf(u32,axiom,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    | r2_hidden(X1,X3) )).

cnf(u45,axiom,
    ( ~ r2_hidden(X0,k1_xboole_0) )).

cnf(u64,negated_conjecture,
    ( k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) )).

cnf(u70,negated_conjecture,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK0) )).

cnf(u23,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u21,negated_conjecture,
    ( k1_xboole_0 != sK0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:31:16 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.37  ipcrm: permission denied for id (820772866)
% 0.15/0.37  ipcrm: permission denied for id (820838404)
% 0.15/0.38  ipcrm: permission denied for id (820903943)
% 0.15/0.38  ipcrm: permission denied for id (820936713)
% 0.15/0.38  ipcrm: permission denied for id (821035021)
% 0.15/0.39  ipcrm: permission denied for id (821133329)
% 0.15/0.39  ipcrm: permission denied for id (821166098)
% 0.15/0.39  ipcrm: permission denied for id (821198867)
% 0.15/0.39  ipcrm: permission denied for id (821231636)
% 0.15/0.40  ipcrm: permission denied for id (821362713)
% 0.15/0.41  ipcrm: permission denied for id (821428253)
% 0.15/0.41  ipcrm: permission denied for id (821493793)
% 0.22/0.42  ipcrm: permission denied for id (821559332)
% 0.22/0.42  ipcrm: permission denied for id (821690409)
% 0.22/0.43  ipcrm: permission denied for id (821755949)
% 0.22/0.43  ipcrm: permission denied for id (821821488)
% 0.22/0.44  ipcrm: permission denied for id (821887026)
% 0.22/0.44  ipcrm: permission denied for id (821919795)
% 0.22/0.44  ipcrm: permission denied for id (821952565)
% 0.22/0.44  ipcrm: permission denied for id (822083641)
% 0.22/0.44  ipcrm: permission denied for id (822116411)
% 0.22/0.45  ipcrm: permission denied for id (822149181)
% 0.22/0.45  ipcrm: permission denied for id (822247488)
% 0.22/0.45  ipcrm: permission denied for id (822476871)
% 0.22/0.45  ipcrm: permission denied for id (822509640)
% 0.22/0.46  ipcrm: permission denied for id (822640716)
% 0.22/0.46  ipcrm: permission denied for id (822673485)
% 0.22/0.46  ipcrm: permission denied for id (822706254)
% 0.22/0.46  ipcrm: permission denied for id (822837331)
% 0.22/0.47  ipcrm: permission denied for id (822935638)
% 0.22/0.47  ipcrm: permission denied for id (823001177)
% 0.22/0.47  ipcrm: permission denied for id (823033946)
% 0.22/0.47  ipcrm: permission denied for id (823099484)
% 0.22/0.48  ipcrm: permission denied for id (823263331)
% 0.22/0.49  ipcrm: permission denied for id (823328870)
% 0.22/0.49  ipcrm: permission denied for id (823361639)
% 0.22/0.49  ipcrm: permission denied for id (823394408)
% 0.22/0.49  ipcrm: permission denied for id (823427177)
% 0.22/0.49  ipcrm: permission denied for id (823459946)
% 0.22/0.49  ipcrm: permission denied for id (823525485)
% 0.22/0.50  ipcrm: permission denied for id (823558254)
% 0.22/0.50  ipcrm: permission denied for id (823591024)
% 0.22/0.50  ipcrm: permission denied for id (823689331)
% 0.22/0.50  ipcrm: permission denied for id (823722100)
% 0.22/0.51  ipcrm: permission denied for id (823853178)
% 0.22/0.51  ipcrm: permission denied for id (823885947)
% 0.22/0.51  ipcrm: permission denied for id (823918716)
% 0.22/0.51  ipcrm: permission denied for id (823951485)
% 1.22/0.67  % (30473)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.22/0.67  % (30464)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.22/0.67  % (30460)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.22/0.67  % (30462)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.22/0.67  % (30472)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.22/0.67  % (30473)Refutation not found, incomplete strategy% (30473)------------------------------
% 1.22/0.67  % (30473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.67  % (30473)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.67  
% 1.22/0.67  % (30473)Memory used [KB]: 6268
% 1.22/0.67  % (30473)Time elapsed: 0.059 s
% 1.22/0.67  % (30473)------------------------------
% 1.22/0.67  % (30473)------------------------------
% 1.22/0.68  % (30449)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.22/0.68  % (30471)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.22/0.68  % (30468)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.22/0.68  % (30453)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.22/0.68  % (30455)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.22/0.68  % (30449)Refutation not found, incomplete strategy% (30449)------------------------------
% 1.22/0.68  % (30449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.68  % (30452)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.22/0.68  % (30449)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.68  
% 1.22/0.68  % (30449)Memory used [KB]: 10746
% 1.22/0.68  % (30449)Time elapsed: 0.074 s
% 1.22/0.68  % (30449)------------------------------
% 1.22/0.68  % (30449)------------------------------
% 1.22/0.68  % (30455)Refutation not found, incomplete strategy% (30455)------------------------------
% 1.22/0.68  % (30455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.68  % (30455)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.68  
% 1.22/0.68  % (30455)Memory used [KB]: 10618
% 1.22/0.68  % (30455)Time elapsed: 0.103 s
% 1.22/0.68  % (30455)------------------------------
% 1.22/0.68  % (30455)------------------------------
% 1.22/0.68  % (30463)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.22/0.69  % (30463)Refutation not found, incomplete strategy% (30463)------------------------------
% 1.22/0.69  % (30463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.69  % (30463)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.69  
% 1.22/0.69  % (30463)Memory used [KB]: 10618
% 1.22/0.69  % (30463)Time elapsed: 0.115 s
% 1.22/0.69  % (30463)------------------------------
% 1.22/0.69  % (30463)------------------------------
% 1.22/0.69  % SZS status CounterSatisfiable for theBenchmark
% 1.22/0.69  % (30452)# SZS output start Saturation.
% 1.22/0.69  cnf(u22,axiom,
% 1.22/0.69      r1_xboole_0(X0,k1_xboole_0)).
% 1.22/0.69  
% 1.22/0.69  cnf(u27,axiom,
% 1.22/0.69      ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))).
% 1.22/0.69  
% 1.22/0.69  cnf(u33,axiom,
% 1.22/0.69      r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)).
% 1.22/0.69  
% 1.22/0.69  cnf(u28,axiom,
% 1.22/0.69      r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)).
% 1.22/0.69  
% 1.22/0.69  cnf(u25,axiom,
% 1.22/0.69      r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0).
% 1.22/0.69  
% 1.22/0.69  cnf(u31,axiom,
% 1.22/0.69      ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)).
% 1.22/0.69  
% 1.22/0.69  cnf(u32,axiom,
% 1.22/0.69      ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)).
% 1.22/0.69  
% 1.22/0.69  cnf(u45,axiom,
% 1.22/0.69      ~r2_hidden(X0,k1_xboole_0)).
% 1.22/0.69  
% 1.22/0.69  cnf(u64,negated_conjecture,
% 1.22/0.69      k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)).
% 1.22/0.69  
% 1.22/0.69  cnf(u70,negated_conjecture,
% 1.22/0.69      k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK0)).
% 1.22/0.69  
% 1.22/0.69  cnf(u23,axiom,
% 1.22/0.69      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 1.22/0.69  
% 1.22/0.69  cnf(u21,negated_conjecture,
% 1.22/0.69      k1_xboole_0 != sK0).
% 1.22/0.69  
% 1.22/0.69  % (30452)# SZS output end Saturation.
% 1.22/0.69  % (30452)------------------------------
% 1.22/0.69  % (30452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.69  % (30452)Termination reason: Satisfiable
% 1.22/0.69  
% 1.22/0.69  % (30452)Memory used [KB]: 6140
% 1.22/0.69  % (30452)Time elapsed: 0.115 s
% 1.22/0.69  % (30452)------------------------------
% 1.22/0.69  % (30452)------------------------------
% 1.22/0.69  % (30284)Success in time 0.328 s
%------------------------------------------------------------------------------
