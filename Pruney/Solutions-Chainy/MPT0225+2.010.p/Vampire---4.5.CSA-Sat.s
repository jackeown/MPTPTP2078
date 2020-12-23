%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:07 EST 2020

% Result     : CounterSatisfiable 1.51s
% Output     : Saturation 1.51s
% Verified   : 
% Statistics : Number of clauses        :   42 (  42 expanded)
%              Number of leaves         :   42 (  42 expanded)
%              Depth                    :    0
%              Number of atoms          :   65 (  65 expanded)
%              Number of equality atoms :   56 (  56 expanded)
%              Maximal clause size      :    2 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u131,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,k5_enumset1(X13,X13,X13,sK0,sK0,sK0,sK0))
    | sK0 = X13 )).

cnf(u93,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,k5_enumset1(X5,X5,X5,X5,X5,X5,X5))
    | sK0 = X5 )).

cnf(u153,negated_conjecture,
    ( r1_xboole_0(k5_enumset1(X3,X3,X3,sK0,sK0,sK0,sK0),k5_enumset1(X2,X2,X2,sK0,sK0,sK0,sK0))
    | X2 = X3 )).

cnf(u124,negated_conjecture,
    ( r1_xboole_0(k5_enumset1(X0,X0,X0,sK0,sK0,sK0,sK0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 )).

cnf(u130,negated_conjecture,
    ( r1_xboole_0(k5_enumset1(X12,X12,X12,sK0,sK0,sK0,sK0),k1_xboole_0)
    | sK0 = X12 )).

cnf(u92,negated_conjecture,
    ( r1_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X4),k1_xboole_0)
    | sK0 = X4 )).

cnf(u125,negated_conjecture,
    ( r1_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X3),k5_enumset1(X2,X2,X2,sK0,sK0,sK0,sK0))
    | X2 = X3 )).

cnf(u58,axiom,
    ( r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 )).

cnf(u59,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 )).

cnf(u74,negated_conjecture,
    ( sK0 = sK1 )).

cnf(u122,negated_conjecture,
    ( k5_enumset1(X3,X3,X3,X3,X3,X4,X5) = k5_enumset1(X3,X4,X5,sK0,sK0,sK0,sK0) )).

cnf(u136,negated_conjecture,
    ( k5_enumset1(sK0,sK0,sK0,X37,X37,X38,X39) = k5_xboole_0(k1_xboole_0,k5_enumset1(X37,X38,X39,sK0,sK0,sK0,sK0)) )).

cnf(u101,negated_conjecture,
    ( k5_enumset1(sK0,sK0,sK0,X6,X7,X8,X9) = k5_xboole_0(k1_xboole_0,k5_enumset1(X6,X6,X6,X6,X7,X8,X9)) )).

cnf(u167,negated_conjecture,
    ( k5_enumset1(X3,X3,X3,X2,X2,X2,X2) = k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X3),k5_enumset1(X2,X2,X2,sK0,sK0,sK0,sK0))
    | X2 = X3 )).

cnf(u173,negated_conjecture,
    ( k5_enumset1(X3,X3,X3,X2,X2,X2,X2) = k5_xboole_0(k5_enumset1(X3,X3,X3,sK0,sK0,sK0,sK0),k5_enumset1(X2,X2,X2,sK0,sK0,sK0,sK0))
    | X2 = X3 )).

cnf(u165,negated_conjecture,
    ( k5_enumset1(X2,X2,X2,X3,X3,X3,X3) = k5_xboole_0(k5_enumset1(X2,X2,X2,sK0,sK0,sK0,sK0),k5_enumset1(X3,X3,X3,X3,X3,X3,X3))
    | X2 = X3 )).

cnf(u103,negated_conjecture,
    ( k5_enumset1(X10,X11,X12,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(X10,X10,X10,X10,X10,X11,X12),k1_xboole_0) )).

cnf(u352,negated_conjecture,
    ( k5_enumset1(X11,X12,X13,X8,X8,X9,X10) = k5_xboole_0(k5_enumset1(X11,X12,X13,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(X8,X9,X10,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(X8,X9,X10,sK0,sK0,sK0,sK0),k5_enumset1(X11,X12,X13,sK0,sK0,sK0,sK0)))) )).

cnf(u270,negated_conjecture,
    ( k5_enumset1(X11,X12,X13,X8,X8,X9,X10) = k5_xboole_0(k5_enumset1(X11,X12,X13,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(X8,X9,X10,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(X11,X12,X13,sK0,sK0,sK0,sK0),k5_enumset1(X8,X9,X10,sK0,sK0,sK0,sK0)))) )).

cnf(u137,negated_conjecture,
    ( k5_enumset1(X43,X44,X45,X40,X40,X41,X42) = k5_xboole_0(k5_enumset1(X43,X43,X43,X43,X43,X44,X45),k5_xboole_0(k5_enumset1(X40,X41,X42,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(X40,X41,X42,sK0,sK0,sK0,sK0),k5_enumset1(X43,X43,X43,X43,X43,X44,X45)))) )).

cnf(u135,negated_conjecture,
    ( k5_enumset1(X34,X35,X36,X31,X31,X32,X33) = k5_xboole_0(k5_enumset1(X34,X34,X34,X34,X34,X35,X36),k5_xboole_0(k5_enumset1(X31,X32,X33,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(X34,X34,X34,X34,X34,X35,X36),k5_enumset1(X31,X32,X33,sK0,sK0,sK0,sK0)))) )).

cnf(u134,negated_conjecture,
    ( k5_enumset1(X24,X25,X26,X27,X28,X29,X30) = k5_xboole_0(k5_enumset1(X24,X25,X26,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(X27,X27,X27,X27,X28,X29,X30),k3_xboole_0(k5_enumset1(X27,X27,X27,X27,X28,X29,X30),k5_enumset1(X24,X25,X26,sK0,sK0,sK0,sK0)))) )).

cnf(u133,negated_conjecture,
    ( k5_enumset1(X17,X18,X19,X20,X21,X22,X23) = k5_xboole_0(k5_enumset1(X17,X18,X19,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(X20,X20,X20,X20,X21,X22,X23),k3_xboole_0(k5_enumset1(X17,X18,X19,sK0,sK0,sK0,sK0),k5_enumset1(X20,X20,X20,X20,X21,X22,X23)))) )).

cnf(u80,axiom,
    ( k5_enumset1(X4,X5,X6,X0,X1,X2,X3) = k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X1,X2,X3)))) )).

cnf(u55,axiom,
    ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2)))) )).

cnf(u246,negated_conjecture,
    ( k5_enumset1(X3,X3,X3,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(X3,X3,X3,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(X2,X2,X2,sK0,sK0,sK0,sK0),k5_enumset1(X3,X3,X3,sK0,sK0,sK0,sK0)))
    | X2 = X3 )).

cnf(u128,negated_conjecture,
    ( k5_enumset1(X8,X8,X8,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(X8,X8,X8,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(X9,X9,X9,X9,X9,X9,X9),k5_enumset1(X8,X8,X8,sK0,sK0,sK0,sK0)))
    | X8 = X9 )).

cnf(u159,negated_conjecture,
    ( k5_enumset1(X1,X1,X1,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(X1,X1,X1,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(X1,X1,X1,sK0,sK0,sK0,sK0),k5_enumset1(X0,X0,X0,sK0,sK0,sK0,sK0)))
    | X0 = X1 )).

cnf(u126,negated_conjecture,
    ( k5_enumset1(X4,X4,X4,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(X4,X4,X4,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(X4,X4,X4,sK0,sK0,sK0,sK0),k5_enumset1(X5,X5,X5,X5,X5,X5,X5)))
    | X4 = X5 )).

cnf(u129,negated_conjecture,
    ( k5_enumset1(X11,X11,X11,X11,X11,X11,X11) = k5_xboole_0(k5_enumset1(X11,X11,X11,X11,X11,X11,X11),k3_xboole_0(k5_enumset1(X10,X10,X10,sK0,sK0,sK0,sK0),k5_enumset1(X11,X11,X11,X11,X11,X11,X11)))
    | X10 = X11 )).

cnf(u70,axiom,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))
    | X0 = X1 )).

cnf(u127,negated_conjecture,
    ( k5_enumset1(X7,X7,X7,X7,X7,X7,X7) = k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X6,X6,X6,sK0,sK0,sK0,sK0)))
    | X6 = X7 )).

cnf(u69,axiom,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))
    | X0 = X1 )).

cnf(u85,negated_conjecture,
    ( k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) )).

cnf(u31,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u61,axiom,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

cnf(u30,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u310,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(X8,X8,X8,sK0,sK0,sK0,sK0),k5_enumset1(X7,X7,X7,X7,X7,X7,X7)) = k5_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k5_enumset1(X7,X7,X7,X7,X7,X7,X7))
    | X7 = X8 )).

cnf(u221,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X4),k5_enumset1(X5,X5,X5,sK0,sK0,sK0,sK0)) = k5_xboole_0(k5_enumset1(X4,X4,X4,sK0,sK0,sK0,sK0),k5_enumset1(X5,X5,X5,sK0,sK0,sK0,sK0))
    | X4 = X5 )).

cnf(u82,axiom,
    ( k5_enumset1(X1,X1,X1,X0,X0,X0,X0) = k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))
    | X0 = X1 )).

cnf(u32,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u34,axiom,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:30:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (8034)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (8038)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (8046)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (8037)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (8038)Refutation not found, incomplete strategy% (8038)------------------------------
% 0.22/0.54  % (8038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8037)Refutation not found, incomplete strategy% (8037)------------------------------
% 0.22/0.54  % (8037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8037)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8037)Memory used [KB]: 10618
% 0.22/0.54  % (8037)Time elapsed: 0.109 s
% 0.22/0.54  % (8037)------------------------------
% 0.22/0.54  % (8037)------------------------------
% 0.22/0.54  % (8054)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (8038)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8038)Memory used [KB]: 10618
% 0.22/0.54  % (8038)Time elapsed: 0.113 s
% 0.22/0.54  % (8038)------------------------------
% 0.22/0.54  % (8038)------------------------------
% 0.22/0.54  % (8050)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (8054)Refutation not found, incomplete strategy% (8054)------------------------------
% 0.22/0.55  % (8054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (8042)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.32/0.55  % (8054)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (8054)Memory used [KB]: 10746
% 1.32/0.55  % (8054)Time elapsed: 0.125 s
% 1.32/0.55  % (8054)------------------------------
% 1.32/0.55  % (8054)------------------------------
% 1.32/0.55  % (8053)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.32/0.56  % (8036)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.32/0.56  % (8039)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.32/0.56  % (8045)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.32/0.56  % (8045)Refutation not found, incomplete strategy% (8045)------------------------------
% 1.32/0.56  % (8045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (8031)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.56  % (8045)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (8045)Memory used [KB]: 10618
% 1.32/0.56  % (8045)Time elapsed: 0.127 s
% 1.32/0.56  % (8045)------------------------------
% 1.32/0.56  % (8045)------------------------------
% 1.32/0.56  % (8030)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.51/0.57  % (8051)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.51/0.57  % (8035)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.51/0.57  % (8057)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.51/0.57  % (8055)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.51/0.57  % (8052)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.51/0.57  % (8043)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.51/0.57  % (8056)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.51/0.57  % (8040)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.51/0.57  % (8029)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.51/0.58  % (8032)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.51/0.58  % (8047)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.51/0.58  % (8048)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.51/0.58  % (8036)Refutation not found, incomplete strategy% (8036)------------------------------
% 1.51/0.58  % (8036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.58  % (8036)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.58  
% 1.51/0.58  % (8036)Memory used [KB]: 10618
% 1.51/0.58  % (8036)Time elapsed: 0.160 s
% 1.51/0.58  % (8036)------------------------------
% 1.51/0.58  % (8036)------------------------------
% 1.51/0.58  % (8039)Refutation not found, incomplete strategy% (8039)------------------------------
% 1.51/0.58  % (8039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.58  % (8030)Refutation not found, incomplete strategy% (8030)------------------------------
% 1.51/0.58  % (8030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.58  % (8030)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.58  
% 1.51/0.58  % (8030)Memory used [KB]: 10618
% 1.51/0.58  % (8030)Time elapsed: 0.152 s
% 1.51/0.58  % (8030)------------------------------
% 1.51/0.58  % (8030)------------------------------
% 1.51/0.58  % (8028)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.51/0.58  % (8048)Refutation not found, incomplete strategy% (8048)------------------------------
% 1.51/0.58  % (8048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.58  % (8048)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.58  
% 1.51/0.58  % (8048)Memory used [KB]: 10746
% 1.51/0.58  % (8048)Time elapsed: 0.160 s
% 1.51/0.58  % (8048)------------------------------
% 1.51/0.58  % (8048)------------------------------
% 1.51/0.58  % (8051)Refutation not found, incomplete strategy% (8051)------------------------------
% 1.51/0.58  % (8051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.58  % (8051)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.58  
% 1.51/0.58  % (8051)Memory used [KB]: 1663
% 1.51/0.58  % (8051)Time elapsed: 0.161 s
% 1.51/0.58  % (8051)------------------------------
% 1.51/0.58  % (8051)------------------------------
% 1.51/0.58  % (8044)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.51/0.58  % (8039)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.58  
% 1.51/0.58  % (8039)Memory used [KB]: 10618
% 1.51/0.58  % (8039)Time elapsed: 0.159 s
% 1.51/0.58  % (8039)------------------------------
% 1.51/0.58  % (8039)------------------------------
% 1.51/0.58  % (8032)Refutation not found, incomplete strategy% (8032)------------------------------
% 1.51/0.58  % (8032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.59  % (8032)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.59  
% 1.51/0.59  % (8032)Memory used [KB]: 6140
% 1.51/0.59  % (8032)Time elapsed: 0.150 s
% 1.51/0.59  % (8032)------------------------------
% 1.51/0.59  % (8032)------------------------------
% 1.51/0.59  % (8041)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.51/0.59  % (8033)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.51/0.59  % (8049)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.51/0.59  % (8049)Refutation not found, incomplete strategy% (8049)------------------------------
% 1.51/0.59  % (8049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.59  % (8043)Refutation not found, incomplete strategy% (8043)------------------------------
% 1.51/0.59  % (8043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.59  % (8043)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.59  
% 1.51/0.59  % (8043)Memory used [KB]: 6140
% 1.51/0.59  % (8043)Time elapsed: 0.003 s
% 1.51/0.59  % (8043)------------------------------
% 1.51/0.59  % (8043)------------------------------
% 1.51/0.60  % (8049)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.60  
% 1.51/0.60  % (8049)Memory used [KB]: 1663
% 1.51/0.60  % (8049)Time elapsed: 0.143 s
% 1.51/0.60  % (8049)------------------------------
% 1.51/0.60  % (8049)------------------------------
% 1.51/0.60  % (8028)Refutation not found, incomplete strategy% (8028)------------------------------
% 1.51/0.60  % (8028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.60  % (8028)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.60  
% 1.51/0.60  % (8028)Memory used [KB]: 1663
% 1.51/0.60  % (8028)Time elapsed: 0.161 s
% 1.51/0.60  % (8028)------------------------------
% 1.51/0.60  % (8028)------------------------------
% 1.51/0.61  % SZS status CounterSatisfiable for theBenchmark
% 1.51/0.61  % (8034)# SZS output start Saturation.
% 1.51/0.61  cnf(u131,negated_conjecture,
% 1.51/0.61      r1_xboole_0(k1_xboole_0,k5_enumset1(X13,X13,X13,sK0,sK0,sK0,sK0)) | sK0 = X13).
% 1.51/0.61  
% 1.51/0.61  cnf(u93,negated_conjecture,
% 1.51/0.61      r1_xboole_0(k1_xboole_0,k5_enumset1(X5,X5,X5,X5,X5,X5,X5)) | sK0 = X5).
% 1.51/0.61  
% 1.51/0.61  cnf(u153,negated_conjecture,
% 1.51/0.61      r1_xboole_0(k5_enumset1(X3,X3,X3,sK0,sK0,sK0,sK0),k5_enumset1(X2,X2,X2,sK0,sK0,sK0,sK0)) | X2 = X3).
% 1.51/0.61  
% 1.51/0.61  cnf(u124,negated_conjecture,
% 1.51/0.61      r1_xboole_0(k5_enumset1(X0,X0,X0,sK0,sK0,sK0,sK0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | X0 = X1).
% 1.51/0.61  
% 1.51/0.61  cnf(u130,negated_conjecture,
% 1.51/0.61      r1_xboole_0(k5_enumset1(X12,X12,X12,sK0,sK0,sK0,sK0),k1_xboole_0) | sK0 = X12).
% 1.51/0.61  
% 1.51/0.61  cnf(u92,negated_conjecture,
% 1.51/0.61      r1_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X4),k1_xboole_0) | sK0 = X4).
% 1.51/0.61  
% 1.51/0.61  cnf(u125,negated_conjecture,
% 1.51/0.61      r1_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X3),k5_enumset1(X2,X2,X2,sK0,sK0,sK0,sK0)) | X2 = X3).
% 1.51/0.61  
% 1.51/0.61  cnf(u58,axiom,
% 1.51/0.61      r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | X0 = X1).
% 1.51/0.61  
% 1.51/0.61  cnf(u59,axiom,
% 1.51/0.61      ~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0).
% 1.51/0.61  
% 1.51/0.61  cnf(u74,negated_conjecture,
% 1.51/0.61      sK0 = sK1).
% 1.51/0.61  
% 1.51/0.61  cnf(u122,negated_conjecture,
% 1.51/0.61      k5_enumset1(X3,X3,X3,X3,X3,X4,X5) = k5_enumset1(X3,X4,X5,sK0,sK0,sK0,sK0)).
% 1.51/0.61  
% 1.51/0.61  cnf(u136,negated_conjecture,
% 1.51/0.61      k5_enumset1(sK0,sK0,sK0,X37,X37,X38,X39) = k5_xboole_0(k1_xboole_0,k5_enumset1(X37,X38,X39,sK0,sK0,sK0,sK0))).
% 1.51/0.61  
% 1.51/0.61  cnf(u101,negated_conjecture,
% 1.51/0.61      k5_enumset1(sK0,sK0,sK0,X6,X7,X8,X9) = k5_xboole_0(k1_xboole_0,k5_enumset1(X6,X6,X6,X6,X7,X8,X9))).
% 1.51/0.61  
% 1.51/0.61  cnf(u167,negated_conjecture,
% 1.51/0.61      k5_enumset1(X3,X3,X3,X2,X2,X2,X2) = k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X3),k5_enumset1(X2,X2,X2,sK0,sK0,sK0,sK0)) | X2 = X3).
% 1.51/0.61  
% 1.51/0.61  cnf(u173,negated_conjecture,
% 1.51/0.61      k5_enumset1(X3,X3,X3,X2,X2,X2,X2) = k5_xboole_0(k5_enumset1(X3,X3,X3,sK0,sK0,sK0,sK0),k5_enumset1(X2,X2,X2,sK0,sK0,sK0,sK0)) | X2 = X3).
% 1.51/0.61  
% 1.51/0.61  cnf(u165,negated_conjecture,
% 1.51/0.61      k5_enumset1(X2,X2,X2,X3,X3,X3,X3) = k5_xboole_0(k5_enumset1(X2,X2,X2,sK0,sK0,sK0,sK0),k5_enumset1(X3,X3,X3,X3,X3,X3,X3)) | X2 = X3).
% 1.51/0.61  
% 1.51/0.61  cnf(u103,negated_conjecture,
% 1.51/0.61      k5_enumset1(X10,X11,X12,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(X10,X10,X10,X10,X10,X11,X12),k1_xboole_0)).
% 1.51/0.61  
% 1.51/0.61  cnf(u352,negated_conjecture,
% 1.51/0.61      k5_enumset1(X11,X12,X13,X8,X8,X9,X10) = k5_xboole_0(k5_enumset1(X11,X12,X13,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(X8,X9,X10,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(X8,X9,X10,sK0,sK0,sK0,sK0),k5_enumset1(X11,X12,X13,sK0,sK0,sK0,sK0))))).
% 1.51/0.61  
% 1.51/0.61  cnf(u270,negated_conjecture,
% 1.51/0.61      k5_enumset1(X11,X12,X13,X8,X8,X9,X10) = k5_xboole_0(k5_enumset1(X11,X12,X13,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(X8,X9,X10,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(X11,X12,X13,sK0,sK0,sK0,sK0),k5_enumset1(X8,X9,X10,sK0,sK0,sK0,sK0))))).
% 1.51/0.61  
% 1.51/0.61  cnf(u137,negated_conjecture,
% 1.51/0.61      k5_enumset1(X43,X44,X45,X40,X40,X41,X42) = k5_xboole_0(k5_enumset1(X43,X43,X43,X43,X43,X44,X45),k5_xboole_0(k5_enumset1(X40,X41,X42,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(X40,X41,X42,sK0,sK0,sK0,sK0),k5_enumset1(X43,X43,X43,X43,X43,X44,X45))))).
% 1.51/0.61  
% 1.51/0.61  cnf(u135,negated_conjecture,
% 1.51/0.61      k5_enumset1(X34,X35,X36,X31,X31,X32,X33) = k5_xboole_0(k5_enumset1(X34,X34,X34,X34,X34,X35,X36),k5_xboole_0(k5_enumset1(X31,X32,X33,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(X34,X34,X34,X34,X34,X35,X36),k5_enumset1(X31,X32,X33,sK0,sK0,sK0,sK0))))).
% 1.51/0.61  
% 1.51/0.61  cnf(u134,negated_conjecture,
% 1.51/0.61      k5_enumset1(X24,X25,X26,X27,X28,X29,X30) = k5_xboole_0(k5_enumset1(X24,X25,X26,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(X27,X27,X27,X27,X28,X29,X30),k3_xboole_0(k5_enumset1(X27,X27,X27,X27,X28,X29,X30),k5_enumset1(X24,X25,X26,sK0,sK0,sK0,sK0))))).
% 1.51/0.61  
% 1.51/0.61  cnf(u133,negated_conjecture,
% 1.51/0.61      k5_enumset1(X17,X18,X19,X20,X21,X22,X23) = k5_xboole_0(k5_enumset1(X17,X18,X19,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(X20,X20,X20,X20,X21,X22,X23),k3_xboole_0(k5_enumset1(X17,X18,X19,sK0,sK0,sK0,sK0),k5_enumset1(X20,X20,X20,X20,X21,X22,X23))))).
% 1.51/0.61  
% 1.51/0.61  cnf(u80,axiom,
% 1.51/0.61      k5_enumset1(X4,X5,X6,X0,X1,X2,X3) = k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k3_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X1,X2,X3))))).
% 1.51/0.61  
% 1.51/0.61  cnf(u55,axiom,
% 1.51/0.61      k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X0,X1,X2))))).
% 1.51/0.61  
% 1.51/0.61  cnf(u246,negated_conjecture,
% 1.51/0.61      k5_enumset1(X3,X3,X3,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(X3,X3,X3,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(X2,X2,X2,sK0,sK0,sK0,sK0),k5_enumset1(X3,X3,X3,sK0,sK0,sK0,sK0))) | X2 = X3).
% 1.51/0.61  
% 1.51/0.61  cnf(u128,negated_conjecture,
% 1.51/0.61      k5_enumset1(X8,X8,X8,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(X8,X8,X8,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(X9,X9,X9,X9,X9,X9,X9),k5_enumset1(X8,X8,X8,sK0,sK0,sK0,sK0))) | X8 = X9).
% 1.51/0.61  
% 1.51/0.61  cnf(u159,negated_conjecture,
% 1.51/0.61      k5_enumset1(X1,X1,X1,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(X1,X1,X1,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(X1,X1,X1,sK0,sK0,sK0,sK0),k5_enumset1(X0,X0,X0,sK0,sK0,sK0,sK0))) | X0 = X1).
% 1.51/0.61  
% 1.51/0.61  cnf(u126,negated_conjecture,
% 1.51/0.61      k5_enumset1(X4,X4,X4,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_enumset1(X4,X4,X4,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(X4,X4,X4,sK0,sK0,sK0,sK0),k5_enumset1(X5,X5,X5,X5,X5,X5,X5))) | X4 = X5).
% 1.51/0.61  
% 1.51/0.61  cnf(u129,negated_conjecture,
% 1.51/0.61      k5_enumset1(X11,X11,X11,X11,X11,X11,X11) = k5_xboole_0(k5_enumset1(X11,X11,X11,X11,X11,X11,X11),k3_xboole_0(k5_enumset1(X10,X10,X10,sK0,sK0,sK0,sK0),k5_enumset1(X11,X11,X11,X11,X11,X11,X11))) | X10 = X11).
% 1.51/0.61  
% 1.51/0.61  cnf(u70,axiom,
% 1.51/0.61      k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) | X0 = X1).
% 1.51/0.61  
% 1.51/0.61  cnf(u127,negated_conjecture,
% 1.51/0.61      k5_enumset1(X7,X7,X7,X7,X7,X7,X7) = k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X6,X6,X6,sK0,sK0,sK0,sK0))) | X6 = X7).
% 1.51/0.61  
% 1.51/0.61  cnf(u69,axiom,
% 1.51/0.61      k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) | X0 = X1).
% 1.51/0.61  
% 1.51/0.61  cnf(u85,negated_conjecture,
% 1.51/0.61      k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)).
% 1.51/0.61  
% 1.51/0.61  cnf(u31,axiom,
% 1.51/0.61      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 1.51/0.61  
% 1.51/0.61  cnf(u61,axiom,
% 1.51/0.61      k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)).
% 1.51/0.61  
% 1.51/0.61  cnf(u30,axiom,
% 1.51/0.61      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 1.51/0.61  
% 1.51/0.61  cnf(u310,negated_conjecture,
% 1.51/0.61      k5_xboole_0(k5_enumset1(X8,X8,X8,sK0,sK0,sK0,sK0),k5_enumset1(X7,X7,X7,X7,X7,X7,X7)) = k5_xboole_0(k5_enumset1(X8,X8,X8,X8,X8,X8,X8),k5_enumset1(X7,X7,X7,X7,X7,X7,X7)) | X7 = X8).
% 1.51/0.61  
% 1.51/0.61  cnf(u221,negated_conjecture,
% 1.51/0.61      k5_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X4,X4),k5_enumset1(X5,X5,X5,sK0,sK0,sK0,sK0)) = k5_xboole_0(k5_enumset1(X4,X4,X4,sK0,sK0,sK0,sK0),k5_enumset1(X5,X5,X5,sK0,sK0,sK0,sK0)) | X4 = X5).
% 1.51/0.61  
% 1.51/0.61  cnf(u82,axiom,
% 1.51/0.61      k5_enumset1(X1,X1,X1,X0,X0,X0,X0) = k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) | X0 = X1).
% 1.51/0.61  
% 1.51/0.61  cnf(u32,axiom,
% 1.51/0.61      k5_xboole_0(X0,k1_xboole_0) = X0).
% 1.51/0.61  
% 1.51/0.61  cnf(u34,axiom,
% 1.51/0.61      k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)).
% 1.51/0.61  
% 1.51/0.61  % (8034)# SZS output end Saturation.
% 1.51/0.61  % (8034)------------------------------
% 1.51/0.61  % (8034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.61  % (8034)Termination reason: Satisfiable
% 1.51/0.61  
% 1.51/0.61  % (8034)Memory used [KB]: 6652
% 1.51/0.61  % (8034)Time elapsed: 0.186 s
% 1.51/0.61  % (8034)------------------------------
% 1.51/0.61  % (8034)------------------------------
% 1.51/0.63  % (8027)Success in time 0.257 s
%------------------------------------------------------------------------------
