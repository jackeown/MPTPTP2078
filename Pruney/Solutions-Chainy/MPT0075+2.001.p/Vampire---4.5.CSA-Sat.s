%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:38 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   66 (  66 expanded)
%              Number of leaves         :   66 (  66 expanded)
%              Depth                    :    0
%              Number of atoms          :  142 ( 142 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u22,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u18,negated_conjecture,
    ( ~ v1_xboole_0(sK2) )).

cnf(u134,negated_conjecture,
    ( r1_xboole_0(sK2,X1) )).

cnf(u104,negated_conjecture,
    ( r1_xboole_0(sK2,sK1) )).

cnf(u109,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u32,negated_conjecture,
    ( r1_xboole_0(sK1,sK0) )).

cnf(u21,negated_conjecture,
    ( r1_xboole_0(sK0,sK1) )).

cnf(u42,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,X0) )).

cnf(u138,negated_conjecture,
    ( r1_xboole_0(X5,sK2) )).

cnf(u43,negated_conjecture,
    ( r1_xboole_0(X1,k1_xboole_0) )).

cnf(u237,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1)
    | ~ r1_tarski(k3_xboole_0(X0,X1),sK2) )).

cnf(u133,negated_conjecture,
    ( ~ r1_xboole_0(sK1,X0)
    | r1_xboole_0(sK2,X0) )).

cnf(u233,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1)
    | ~ r1_tarski(k3_xboole_0(X0,X1),sK2) )).

cnf(u103,negated_conjecture,
    ( ~ r1_xboole_0(sK0,X0)
    | r1_xboole_0(sK2,X0) )).

cnf(u102,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK2)
    | r1_xboole_0(sK2,X1) )).

cnf(u195,axiom,
    ( ~ r1_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) )).

cnf(u236,negated_conjecture,
    ( ~ r1_xboole_0(X7,sK1)
    | r1_xboole_0(X5,X6)
    | ~ r2_hidden(sK3(X5,X6),X7)
    | ~ r1_tarski(k3_xboole_0(X5,X6),sK2) )).

cnf(u101,negated_conjecture,
    ( ~ r1_xboole_0(X5,sK0)
    | ~ r2_hidden(sK4(sK2,X4),X5)
    | r1_xboole_0(sK2,X4) )).

cnf(u232,negated_conjecture,
    ( ~ r1_xboole_0(X7,sK0)
    | r1_xboole_0(X5,X6)
    | ~ r2_hidden(sK3(X5,X6),X7)
    | ~ r1_tarski(k3_xboole_0(X5,X6),sK2) )).

cnf(u28,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) )).

cnf(u31,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u34,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X0,X1),X2) )).

cnf(u35,axiom,
    ( ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,k3_xboole_0(X1,X2)) )).

cnf(u180,axiom,
    ( ~ r1_xboole_0(X2,X3)
    | r1_xboole_0(X0,X1)
    | ~ r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) )).

cnf(u87,axiom,
    ( ~ r1_xboole_0(X0,X0)
    | r1_xboole_0(X0,X1) )).

cnf(u92,axiom,
    ( ~ r1_xboole_0(X2,X2)
    | r1_xboole_0(X3,X2) )).

cnf(u229,negated_conjecture,
    ( r2_hidden(sK3(X2,X3),sK1)
    | ~ r1_tarski(k3_xboole_0(X2,X3),sK2)
    | r1_xboole_0(X2,X3) )).

cnf(u228,negated_conjecture,
    ( r2_hidden(sK3(X0,X1),sK0)
    | ~ r1_tarski(k3_xboole_0(X0,X1),sK2)
    | r1_xboole_0(X0,X1) )).

cnf(u24,axiom,
    ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) )).

cnf(u78,axiom,
    ( r2_hidden(sK3(X2,X3),X4)
    | ~ r1_tarski(k3_xboole_0(X2,X3),X4)
    | r1_xboole_0(X2,X3) )).

cnf(u97,negated_conjecture,
    ( r2_hidden(sK4(sK2,X1),sK1)
    | r1_xboole_0(sK2,X1) )).

cnf(u96,negated_conjecture,
    ( r2_hidden(sK4(sK2,X0),sK0)
    | r1_xboole_0(sK2,X0) )).

cnf(u123,negated_conjecture,
    ( r2_hidden(sK4(X1,sK2),sK1)
    | r1_xboole_0(X1,sK2) )).

cnf(u122,negated_conjecture,
    ( r2_hidden(sK4(X0,sK2),sK0)
    | r1_xboole_0(X0,sK2) )).

cnf(u27,axiom,
    ( r2_hidden(sK4(X0,X1),X1)
    | r1_xboole_0(X0,X1) )).

cnf(u26,axiom,
    ( r2_hidden(sK4(X0,X1),X0)
    | r1_xboole_0(X0,X1) )).

cnf(u79,axiom,
    ( ~ r2_hidden(sK3(X5,X6),X7)
    | r1_xboole_0(X5,X6)
    | ~ r1_xboole_0(X7,k3_xboole_0(X5,X6)) )).

cnf(u183,axiom,
    ( ~ r2_hidden(sK3(X10,X11),X13)
    | r1_xboole_0(X10,X11)
    | ~ r1_tarski(k3_xboole_0(X10,X11),X12)
    | ~ r1_xboole_0(X13,X12) )).

cnf(u54,axiom,
    ( ~ r2_hidden(sK4(X0,X1),X2)
    | ~ r1_xboole_0(X2,X0)
    | r1_xboole_0(X0,X1) )).

cnf(u55,axiom,
    ( ~ r2_hidden(sK4(X3,X4),X5)
    | ~ r1_xboole_0(X5,X4)
    | r1_xboole_0(X3,X4) )).

cnf(u25,axiom,
    ( ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r1_xboole_0(X0,X1) )).

cnf(u29,axiom,
    ( ~ r2_hidden(X2,X0)
    | ~ r1_tarski(X0,X1)
    | r2_hidden(X2,X1) )).

cnf(u41,negated_conjecture,
    ( ~ r2_hidden(X0,k1_xboole_0) )).

cnf(u23,axiom,
    ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
    | ~ r1_xboole_0(X0,X1) )).

cnf(u20,negated_conjecture,
    ( r1_tarski(sK2,sK1) )).

cnf(u19,negated_conjecture,
    ( r1_tarski(sK2,sK0) )).

cnf(u235,negated_conjecture,
    ( ~ r1_tarski(sK1,X4)
    | r1_xboole_0(X2,X3)
    | ~ r1_tarski(k3_xboole_0(X2,X3),sK2)
    | r2_hidden(sK3(X2,X3),X4) )).

cnf(u100,negated_conjecture,
    ( ~ r1_tarski(sK0,X3)
    | r1_xboole_0(sK2,X2)
    | r2_hidden(sK4(sK2,X2),X3) )).

cnf(u231,negated_conjecture,
    ( ~ r1_tarski(sK0,X4)
    | r1_xboole_0(X2,X3)
    | ~ r1_tarski(k3_xboole_0(X2,X3),sK2)
    | r2_hidden(sK3(X2,X3),X4) )).

cnf(u257,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(X2,X3),sK2)
    | r1_xboole_0(X2,X3) )).

cnf(u194,axiom,
    ( ~ r1_tarski(k3_xboole_0(X2,X3),X4)
    | ~ r1_xboole_0(X4,k3_xboole_0(X2,X3))
    | r1_xboole_0(X2,X3) )).

cnf(u276,axiom,
    ( ~ r1_tarski(k3_xboole_0(X4,X5),X6)
    | r1_xboole_0(X4,X5)
    | ~ r1_xboole_0(k3_xboole_0(X4,X5),X6) )).

cnf(u277,axiom,
    ( ~ r1_tarski(k3_xboole_0(X0,X1),X3)
    | ~ r1_tarski(k3_xboole_0(X0,X1),X2)
    | ~ r1_xboole_0(X3,X2)
    | r1_xboole_0(X0,X1) )).

cnf(u181,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(X4,X5),k1_xboole_0)
    | r1_xboole_0(X4,X5) )).

cnf(u75,axiom,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(sK4(X0,X2),X1)
    | r1_xboole_0(X0,X2) )).

cnf(u76,axiom,
    ( ~ r1_tarski(X3,X4)
    | r2_hidden(sK4(X5,X3),X4)
    | r1_xboole_0(X5,X3) )).

cnf(u182,axiom,
    ( ~ r1_tarski(X8,X9)
    | r1_xboole_0(X6,X7)
    | ~ r1_tarski(k3_xboole_0(X6,X7),X8)
    | r2_hidden(sK3(X6,X7),X9) )).

cnf(u137,negated_conjecture,
    ( k1_xboole_0 = k3_xboole_0(sK2,X4) )).

cnf(u108,negated_conjecture,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1) )).

cnf(u114,negated_conjecture,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2) )).

cnf(u37,negated_conjecture,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK0) )).

cnf(u36,negated_conjecture,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1) )).

cnf(u44,negated_conjecture,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

cnf(u145,negated_conjecture,
    ( k1_xboole_0 = k3_xboole_0(X4,sK2) )).

cnf(u46,negated_conjecture,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u30,axiom,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:22:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (9166)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.45  % (9166)Refutation not found, incomplete strategy% (9166)------------------------------
% 0.21/0.45  % (9166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (9166)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (9166)Memory used [KB]: 10746
% 0.21/0.46  % (9166)Time elapsed: 0.008 s
% 0.21/0.46  % (9166)------------------------------
% 0.21/0.46  % (9166)------------------------------
% 0.21/0.52  % (9165)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (9205)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 0.21/0.52  % (9165)Refutation not found, incomplete strategy% (9165)------------------------------
% 0.21/0.52  % (9165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9165)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9165)Memory used [KB]: 10618
% 0.21/0.52  % (9165)Time elapsed: 0.111 s
% 0.21/0.52  % (9165)------------------------------
% 0.21/0.52  % (9165)------------------------------
% 0.21/0.52  % (9183)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (9173)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (9158)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (9157)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (9164)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (9159)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (9172)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.57  % (9181)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.57  % (9187)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.57  % (9185)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (9179)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.57  % (9169)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (9189)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.57  % (9171)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.57  % (9188)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.57  % (9174)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.57  % (9161)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.58  % (9170)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.58  % (9170)Refutation not found, incomplete strategy% (9170)------------------------------
% 0.21/0.58  % (9170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (9170)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (9170)Memory used [KB]: 6140
% 0.21/0.58  % (9170)Time elapsed: 0.173 s
% 0.21/0.58  % (9170)------------------------------
% 0.21/0.58  % (9170)------------------------------
% 0.21/0.58  % (9163)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.58  % (9164)Refutation not found, incomplete strategy% (9164)------------------------------
% 0.21/0.58  % (9164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (9164)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (9164)Memory used [KB]: 6396
% 0.21/0.58  % (9164)Time elapsed: 0.132 s
% 0.21/0.58  % (9164)------------------------------
% 0.21/0.58  % (9164)------------------------------
% 0.21/0.58  % (9162)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (9177)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.58  % (9175)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.58  % (9177)Refutation not found, incomplete strategy% (9177)------------------------------
% 0.21/0.58  % (9177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (9177)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (9177)Memory used [KB]: 10618
% 0.21/0.58  % (9177)Time elapsed: 0.181 s
% 0.21/0.58  % (9177)------------------------------
% 0.21/0.58  % (9177)------------------------------
% 0.21/0.58  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.58  % (9163)# SZS output start Saturation.
% 0.21/0.58  cnf(u22,axiom,
% 0.21/0.58      v1_xboole_0(k1_xboole_0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u18,negated_conjecture,
% 0.21/0.58      ~v1_xboole_0(sK2)).
% 0.21/0.58  
% 0.21/0.58  cnf(u134,negated_conjecture,
% 0.21/0.58      r1_xboole_0(sK2,X1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u104,negated_conjecture,
% 0.21/0.58      r1_xboole_0(sK2,sK1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u109,negated_conjecture,
% 0.21/0.58      r1_xboole_0(sK1,sK2)).
% 0.21/0.58  
% 0.21/0.58  cnf(u32,negated_conjecture,
% 0.21/0.58      r1_xboole_0(sK1,sK0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u21,negated_conjecture,
% 0.21/0.58      r1_xboole_0(sK0,sK1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u42,negated_conjecture,
% 0.21/0.58      r1_xboole_0(k1_xboole_0,X0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u138,negated_conjecture,
% 0.21/0.58      r1_xboole_0(X5,sK2)).
% 0.21/0.58  
% 0.21/0.58  cnf(u43,negated_conjecture,
% 0.21/0.58      r1_xboole_0(X1,k1_xboole_0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u237,negated_conjecture,
% 0.21/0.58      ~r1_xboole_0(sK1,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) | ~r1_tarski(k3_xboole_0(X0,X1),sK2)).
% 0.21/0.58  
% 0.21/0.58  cnf(u133,negated_conjecture,
% 0.21/0.58      ~r1_xboole_0(sK1,X0) | r1_xboole_0(sK2,X0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u233,negated_conjecture,
% 0.21/0.58      ~r1_xboole_0(sK0,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) | ~r1_tarski(k3_xboole_0(X0,X1),sK2)).
% 0.21/0.58  
% 0.21/0.58  cnf(u103,negated_conjecture,
% 0.21/0.58      ~r1_xboole_0(sK0,X0) | r1_xboole_0(sK2,X0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u102,negated_conjecture,
% 0.21/0.58      ~r1_xboole_0(sK0,sK2) | r1_xboole_0(sK2,X1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u195,axiom,
% 0.21/0.58      ~r1_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u236,negated_conjecture,
% 0.21/0.58      ~r1_xboole_0(X7,sK1) | r1_xboole_0(X5,X6) | ~r2_hidden(sK3(X5,X6),X7) | ~r1_tarski(k3_xboole_0(X5,X6),sK2)).
% 0.21/0.58  
% 0.21/0.58  cnf(u101,negated_conjecture,
% 0.21/0.58      ~r1_xboole_0(X5,sK0) | ~r2_hidden(sK4(sK2,X4),X5) | r1_xboole_0(sK2,X4)).
% 0.21/0.58  
% 0.21/0.58  cnf(u232,negated_conjecture,
% 0.21/0.58      ~r1_xboole_0(X7,sK0) | r1_xboole_0(X5,X6) | ~r2_hidden(sK3(X5,X6),X7) | ~r1_tarski(k3_xboole_0(X5,X6),sK2)).
% 0.21/0.58  
% 0.21/0.58  cnf(u28,axiom,
% 0.21/0.58      ~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u31,axiom,
% 0.21/0.58      ~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0).
% 0.21/0.58  
% 0.21/0.58  cnf(u34,axiom,
% 0.21/0.58      ~r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X0,X1),X2)).
% 0.21/0.58  
% 0.21/0.58  cnf(u35,axiom,
% 0.21/0.58      ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,k3_xboole_0(X1,X2))).
% 0.21/0.58  
% 0.21/0.58  cnf(u180,axiom,
% 0.21/0.58      ~r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1) | ~r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))).
% 0.21/0.58  
% 0.21/0.58  cnf(u87,axiom,
% 0.21/0.58      ~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u92,axiom,
% 0.21/0.58      ~r1_xboole_0(X2,X2) | r1_xboole_0(X3,X2)).
% 0.21/0.58  
% 0.21/0.58  cnf(u229,negated_conjecture,
% 0.21/0.58      r2_hidden(sK3(X2,X3),sK1) | ~r1_tarski(k3_xboole_0(X2,X3),sK2) | r1_xboole_0(X2,X3)).
% 0.21/0.58  
% 0.21/0.58  cnf(u228,negated_conjecture,
% 0.21/0.58      r2_hidden(sK3(X0,X1),sK0) | ~r1_tarski(k3_xboole_0(X0,X1),sK2) | r1_xboole_0(X0,X1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u24,axiom,
% 0.21/0.58      r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u78,axiom,
% 0.21/0.58      r2_hidden(sK3(X2,X3),X4) | ~r1_tarski(k3_xboole_0(X2,X3),X4) | r1_xboole_0(X2,X3)).
% 0.21/0.58  
% 0.21/0.58  cnf(u97,negated_conjecture,
% 0.21/0.58      r2_hidden(sK4(sK2,X1),sK1) | r1_xboole_0(sK2,X1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u96,negated_conjecture,
% 0.21/0.58      r2_hidden(sK4(sK2,X0),sK0) | r1_xboole_0(sK2,X0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u123,negated_conjecture,
% 0.21/0.58      r2_hidden(sK4(X1,sK2),sK1) | r1_xboole_0(X1,sK2)).
% 0.21/0.58  
% 0.21/0.58  cnf(u122,negated_conjecture,
% 0.21/0.58      r2_hidden(sK4(X0,sK2),sK0) | r1_xboole_0(X0,sK2)).
% 0.21/0.58  
% 0.21/0.58  cnf(u27,axiom,
% 0.21/0.58      r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u26,axiom,
% 0.21/0.58      r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u79,axiom,
% 0.21/0.58      ~r2_hidden(sK3(X5,X6),X7) | r1_xboole_0(X5,X6) | ~r1_xboole_0(X7,k3_xboole_0(X5,X6))).
% 0.21/0.58  
% 0.21/0.58  cnf(u183,axiom,
% 0.21/0.58      ~r2_hidden(sK3(X10,X11),X13) | r1_xboole_0(X10,X11) | ~r1_tarski(k3_xboole_0(X10,X11),X12) | ~r1_xboole_0(X13,X12)).
% 0.21/0.58  
% 0.21/0.58  cnf(u54,axiom,
% 0.21/0.58      ~r2_hidden(sK4(X0,X1),X2) | ~r1_xboole_0(X2,X0) | r1_xboole_0(X0,X1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u55,axiom,
% 0.21/0.58      ~r2_hidden(sK4(X3,X4),X5) | ~r1_xboole_0(X5,X4) | r1_xboole_0(X3,X4)).
% 0.21/0.58  
% 0.21/0.58  cnf(u25,axiom,
% 0.21/0.58      ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u29,axiom,
% 0.21/0.58      ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1) | r2_hidden(X2,X1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u41,negated_conjecture,
% 0.21/0.58      ~r2_hidden(X0,k1_xboole_0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u23,axiom,
% 0.21/0.58      ~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u20,negated_conjecture,
% 0.21/0.58      r1_tarski(sK2,sK1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u19,negated_conjecture,
% 0.21/0.58      r1_tarski(sK2,sK0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u235,negated_conjecture,
% 0.21/0.58      ~r1_tarski(sK1,X4) | r1_xboole_0(X2,X3) | ~r1_tarski(k3_xboole_0(X2,X3),sK2) | r2_hidden(sK3(X2,X3),X4)).
% 0.21/0.58  
% 0.21/0.58  cnf(u100,negated_conjecture,
% 0.21/0.58      ~r1_tarski(sK0,X3) | r1_xboole_0(sK2,X2) | r2_hidden(sK4(sK2,X2),X3)).
% 0.21/0.58  
% 0.21/0.58  cnf(u231,negated_conjecture,
% 0.21/0.58      ~r1_tarski(sK0,X4) | r1_xboole_0(X2,X3) | ~r1_tarski(k3_xboole_0(X2,X3),sK2) | r2_hidden(sK3(X2,X3),X4)).
% 0.21/0.58  
% 0.21/0.58  cnf(u257,negated_conjecture,
% 0.21/0.58      ~r1_tarski(k3_xboole_0(X2,X3),sK2) | r1_xboole_0(X2,X3)).
% 0.21/0.58  
% 0.21/0.58  cnf(u194,axiom,
% 0.21/0.58      ~r1_tarski(k3_xboole_0(X2,X3),X4) | ~r1_xboole_0(X4,k3_xboole_0(X2,X3)) | r1_xboole_0(X2,X3)).
% 0.21/0.58  
% 0.21/0.58  cnf(u276,axiom,
% 0.21/0.58      ~r1_tarski(k3_xboole_0(X4,X5),X6) | r1_xboole_0(X4,X5) | ~r1_xboole_0(k3_xboole_0(X4,X5),X6)).
% 0.21/0.58  
% 0.21/0.58  cnf(u277,axiom,
% 0.21/0.58      ~r1_tarski(k3_xboole_0(X0,X1),X3) | ~r1_tarski(k3_xboole_0(X0,X1),X2) | ~r1_xboole_0(X3,X2) | r1_xboole_0(X0,X1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u181,negated_conjecture,
% 0.21/0.58      ~r1_tarski(k3_xboole_0(X4,X5),k1_xboole_0) | r1_xboole_0(X4,X5)).
% 0.21/0.58  
% 0.21/0.58  cnf(u75,axiom,
% 0.21/0.58      ~r1_tarski(X0,X1) | r2_hidden(sK4(X0,X2),X1) | r1_xboole_0(X0,X2)).
% 0.21/0.58  
% 0.21/0.58  cnf(u76,axiom,
% 0.21/0.58      ~r1_tarski(X3,X4) | r2_hidden(sK4(X5,X3),X4) | r1_xboole_0(X5,X3)).
% 0.21/0.58  
% 0.21/0.58  cnf(u182,axiom,
% 0.21/0.58      ~r1_tarski(X8,X9) | r1_xboole_0(X6,X7) | ~r1_tarski(k3_xboole_0(X6,X7),X8) | r2_hidden(sK3(X6,X7),X9)).
% 0.21/0.58  
% 0.21/0.58  cnf(u137,negated_conjecture,
% 0.21/0.58      k1_xboole_0 = k3_xboole_0(sK2,X4)).
% 0.21/0.58  
% 0.21/0.58  cnf(u108,negated_conjecture,
% 0.21/0.58      k1_xboole_0 = k3_xboole_0(sK2,sK1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u114,negated_conjecture,
% 0.21/0.58      k1_xboole_0 = k3_xboole_0(sK1,sK2)).
% 0.21/0.58  
% 0.21/0.58  cnf(u37,negated_conjecture,
% 0.21/0.58      k1_xboole_0 = k3_xboole_0(sK1,sK0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u36,negated_conjecture,
% 0.21/0.58      k1_xboole_0 = k3_xboole_0(sK0,sK1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u44,negated_conjecture,
% 0.21/0.58      k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u145,negated_conjecture,
% 0.21/0.58      k1_xboole_0 = k3_xboole_0(X4,sK2)).
% 0.21/0.58  
% 0.21/0.58  cnf(u46,negated_conjecture,
% 0.21/0.58      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u30,axiom,
% 0.21/0.58      k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)).
% 0.21/0.58  
% 0.21/0.58  % (9163)# SZS output end Saturation.
% 0.21/0.58  % (9163)------------------------------
% 0.21/0.58  % (9163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (9163)Termination reason: Satisfiable
% 0.21/0.58  
% 0.21/0.58  % (9163)Memory used [KB]: 6268
% 0.21/0.58  % (9163)Time elapsed: 0.176 s
% 0.21/0.58  % (9163)------------------------------
% 0.21/0.58  % (9163)------------------------------
% 0.21/0.58  % (9182)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.59  % (9184)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.60  % (9150)Success in time 0.24 s
%------------------------------------------------------------------------------
