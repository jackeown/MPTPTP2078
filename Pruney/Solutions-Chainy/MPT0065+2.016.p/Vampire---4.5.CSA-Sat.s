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
% DateTime   : Thu Dec  3 12:30:19 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   18 (  18 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    0
%              Number of atoms          :   26 (  26 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u47,negated_conjecture,
    ( r1_tarski(sK1,sK1) )).

cnf(u34,negated_conjecture,
    ( r1_tarski(sK1,sK0) )).

cnf(u39,negated_conjecture,
    ( r1_tarski(sK0,sK0) )).

cnf(u22,negated_conjecture,
    ( r1_tarski(sK0,sK1) )).

cnf(u28,negated_conjecture,
    ( ~ r1_tarski(sK1,X0)
    | r1_tarski(sK0,X0) )).

cnf(u38,negated_conjecture,
    ( ~ r1_tarski(sK0,X0)
    | r1_tarski(sK1,X0) )).

cnf(u20,axiom,
    ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
    | r1_tarski(X0,X2) )).

cnf(u16,axiom,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 )).

cnf(u19,axiom,
    ( ~ r1_tarski(X0,X1)
    | X0 = X1
    | r2_xboole_0(X0,X1) )).

cnf(u40,negated_conjecture,
    ( r2_xboole_0(sK1,sK0)
    | sK0 = sK1 )).

cnf(u12,negated_conjecture,
    ( r2_xboole_0(sK0,sK1) )).

cnf(u17,axiom,
    ( ~ r2_xboole_0(X0,X1)
    | r1_tarski(X0,X1) )).

cnf(u15,axiom,
    ( ~ r2_xboole_0(X0,X0) )).

cnf(u33,negated_conjecture,
    ( sK0 = sK2 )).

cnf(u41,negated_conjecture,
    ( sK0 = k2_xboole_0(sK0,sK0) )).

cnf(u36,negated_conjecture,
    ( sK0 = k2_xboole_0(sK1,sK0) )).

cnf(u50,negated_conjecture,
    ( sK1 = k2_xboole_0(sK1,sK1) )).

cnf(u26,negated_conjecture,
    ( sK1 = k2_xboole_0(sK0,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:41:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (16753)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.47  % (16739)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (16739)Refutation not found, incomplete strategy% (16739)------------------------------
% 0.22/0.48  % (16739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (16739)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (16739)Memory used [KB]: 6140
% 0.22/0.48  % (16739)Time elapsed: 0.007 s
% 0.22/0.48  % (16739)------------------------------
% 0.22/0.48  % (16739)------------------------------
% 0.22/0.48  % (16747)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (16754)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (16754)Refutation not found, incomplete strategy% (16754)------------------------------
% 0.22/0.48  % (16754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (16746)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (16754)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (16754)Memory used [KB]: 6140
% 0.22/0.48  % (16754)Time elapsed: 0.066 s
% 0.22/0.48  % (16754)------------------------------
% 0.22/0.48  % (16754)------------------------------
% 0.22/0.48  % (16741)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (16741)Refutation not found, incomplete strategy% (16741)------------------------------
% 0.22/0.49  % (16741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (16741)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (16741)Memory used [KB]: 10618
% 0.22/0.49  % (16741)Time elapsed: 0.074 s
% 0.22/0.49  % (16741)------------------------------
% 0.22/0.49  % (16741)------------------------------
% 0.22/0.49  % (16755)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (16740)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (16740)Refutation not found, incomplete strategy% (16740)------------------------------
% 0.22/0.49  % (16740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (16740)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (16740)Memory used [KB]: 10490
% 0.22/0.49  % (16740)Time elapsed: 0.076 s
% 0.22/0.49  % (16740)------------------------------
% 0.22/0.49  % (16740)------------------------------
% 0.22/0.49  % (16749)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (16749)Refutation not found, incomplete strategy% (16749)------------------------------
% 0.22/0.50  % (16749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (16749)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (16749)Memory used [KB]: 6012
% 0.22/0.50  % (16749)Time elapsed: 0.087 s
% 0.22/0.50  % (16749)------------------------------
% 0.22/0.50  % (16749)------------------------------
% 0.22/0.50  % (16751)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (16752)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (16751)Refutation not found, incomplete strategy% (16751)------------------------------
% 0.22/0.50  % (16751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (16751)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (16751)Memory used [KB]: 6012
% 0.22/0.50  % (16751)Time elapsed: 0.001 s
% 0.22/0.50  % (16751)------------------------------
% 0.22/0.50  % (16751)------------------------------
% 0.22/0.50  % (16752)Refutation not found, incomplete strategy% (16752)------------------------------
% 0.22/0.50  % (16752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (16752)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (16752)Memory used [KB]: 1535
% 0.22/0.50  % (16752)Time elapsed: 0.085 s
% 0.22/0.50  % (16752)------------------------------
% 0.22/0.50  % (16752)------------------------------
% 0.22/0.50  % (16742)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (16745)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (16745)Refutation not found, incomplete strategy% (16745)------------------------------
% 0.22/0.50  % (16745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (16742)Refutation not found, incomplete strategy% (16742)------------------------------
% 0.22/0.50  % (16742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (16742)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (16742)Memory used [KB]: 10618
% 0.22/0.50  % (16742)Time elapsed: 0.089 s
% 0.22/0.50  % (16742)------------------------------
% 0.22/0.50  % (16742)------------------------------
% 0.22/0.50  % (16756)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % (16750)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.50  % (16756)# SZS output start Saturation.
% 0.22/0.50  cnf(u47,negated_conjecture,
% 0.22/0.50      r1_tarski(sK1,sK1)).
% 0.22/0.50  
% 0.22/0.50  cnf(u34,negated_conjecture,
% 0.22/0.50      r1_tarski(sK1,sK0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u39,negated_conjecture,
% 0.22/0.50      r1_tarski(sK0,sK0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u22,negated_conjecture,
% 0.22/0.50      r1_tarski(sK0,sK1)).
% 0.22/0.50  
% 0.22/0.50  cnf(u28,negated_conjecture,
% 0.22/0.50      ~r1_tarski(sK1,X0) | r1_tarski(sK0,X0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u38,negated_conjecture,
% 0.22/0.50      ~r1_tarski(sK0,X0) | r1_tarski(sK1,X0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u20,axiom,
% 0.22/0.50      ~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)).
% 0.22/0.50  
% 0.22/0.50  cnf(u16,axiom,
% 0.22/0.50      ~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1).
% 0.22/0.50  
% 0.22/0.50  cnf(u19,axiom,
% 0.22/0.50      ~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)).
% 0.22/0.50  
% 0.22/0.50  cnf(u40,negated_conjecture,
% 0.22/0.50      r2_xboole_0(sK1,sK0) | sK0 = sK1).
% 0.22/0.50  
% 0.22/0.50  cnf(u12,negated_conjecture,
% 0.22/0.50      r2_xboole_0(sK0,sK1)).
% 0.22/0.50  
% 0.22/0.50  cnf(u17,axiom,
% 0.22/0.50      ~r2_xboole_0(X0,X1) | r1_tarski(X0,X1)).
% 0.22/0.50  
% 0.22/0.50  cnf(u15,axiom,
% 0.22/0.50      ~r2_xboole_0(X0,X0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u33,negated_conjecture,
% 0.22/0.50      sK0 = sK2).
% 0.22/0.50  
% 0.22/0.50  cnf(u41,negated_conjecture,
% 0.22/0.50      sK0 = k2_xboole_0(sK0,sK0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u36,negated_conjecture,
% 0.22/0.50      sK0 = k2_xboole_0(sK1,sK0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u50,negated_conjecture,
% 0.22/0.50      sK1 = k2_xboole_0(sK1,sK1)).
% 0.22/0.50  
% 0.22/0.50  cnf(u26,negated_conjecture,
% 0.22/0.50      sK1 = k2_xboole_0(sK0,sK1)).
% 0.22/0.50  
% 0.22/0.50  % (16756)# SZS output end Saturation.
% 0.22/0.50  % (16756)------------------------------
% 0.22/0.50  % (16756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (16756)Termination reason: Satisfiable
% 0.22/0.50  
% 0.22/0.50  % (16756)Memory used [KB]: 1663
% 0.22/0.50  % (16756)Time elapsed: 0.089 s
% 0.22/0.50  % (16756)------------------------------
% 0.22/0.50  % (16756)------------------------------
% 0.22/0.50  % (16738)Success in time 0.139 s
%------------------------------------------------------------------------------
