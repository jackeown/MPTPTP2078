%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:30 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    0
%              Number of atoms          :   47 (  47 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u159,axiom,(
    ! [X1,X0] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) )).

tff(u158,axiom,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 )).

tff(u157,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u156,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) )).

tff(u155,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) )).

tff(u154,negated_conjecture,
    ( ~ v1_xboole_0(sK1)
    | ! [X3] : k1_xboole_0 = k4_xboole_0(sK1,X3) )).

tff(u153,negated_conjecture,
    ( k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) )).

tff(u152,axiom,(
    ! [X1,X0] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) )).

tff(u151,negated_conjecture,
    ( k1_xboole_0 != k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1))
    | k1_xboole_0 = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1)) )).

tff(u150,negated_conjecture,
    ( sK0 != k3_tarski(k1_xboole_0)
    | sK0 = k3_tarski(k1_xboole_0) )).

tff(u149,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(X0)
      | r1_tarski(X0,X1) ) )).

tff(u148,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)))
      | v1_xboole_0(X0) ) )).

tff(u147,axiom,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) )).

tff(u146,negated_conjecture,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK1) )).

tff(u145,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) )).

tff(u144,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) )).

tff(u143,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) )).

tff(u142,axiom,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) )).

tff(u141,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) )).

tff(u140,axiom,(
    ! [X3,X2,X4] :
      ( ~ r1_tarski(X2,X4)
      | r2_hidden(sK3(X2,X3),X4)
      | r1_tarski(X2,X3) ) )).

tff(u139,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(sK2(X0),X1)
      | v1_xboole_0(X0) ) )).

tff(u138,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) )).

tff(u137,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u136,axiom,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ! [X0] : r1_tarski(k1_xboole_0,X0) )).

tff(u135,negated_conjecture,
    ( ~ v1_xboole_0(sK1)
    | ! [X0] : r1_tarski(sK1,X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (14117)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.48  % (14111)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.48  % (14101)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.49  % (14113)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.49  % (14115)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.49  % (14100)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.49  % (14106)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (14099)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.49  % (14094)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.49  % (14094)Refutation not found, incomplete strategy% (14094)------------------------------
% 0.21/0.49  % (14094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (14114)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.49  % (14094)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (14094)Memory used [KB]: 1663
% 0.21/0.49  % (14094)Time elapsed: 0.070 s
% 0.21/0.49  % (14094)------------------------------
% 0.21/0.49  % (14094)------------------------------
% 0.21/0.49  % (14098)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (14098)Refutation not found, incomplete strategy% (14098)------------------------------
% 0.21/0.49  % (14098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (14098)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (14098)Memory used [KB]: 6140
% 0.21/0.49  % (14098)Time elapsed: 0.094 s
% 0.21/0.49  % (14098)------------------------------
% 0.21/0.49  % (14098)------------------------------
% 0.21/0.50  % (14122)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.50  % (14115)Refutation not found, incomplete strategy% (14115)------------------------------
% 0.21/0.50  % (14115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14115)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (14115)Memory used [KB]: 1663
% 0.21/0.50  % (14115)Time elapsed: 0.110 s
% 0.21/0.50  % (14115)------------------------------
% 0.21/0.50  % (14115)------------------------------
% 0.21/0.50  % (14116)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (14121)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.50  % (14103)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (14096)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (14107)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (14103)Refutation not found, incomplete strategy% (14103)------------------------------
% 0.21/0.50  % (14103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14103)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (14103)Memory used [KB]: 10618
% 0.21/0.50  % (14103)Time elapsed: 0.104 s
% 0.21/0.50  % (14103)------------------------------
% 0.21/0.50  % (14103)------------------------------
% 0.21/0.50  % (14116)Refutation not found, incomplete strategy% (14116)------------------------------
% 0.21/0.50  % (14116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14116)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (14116)Memory used [KB]: 10746
% 0.21/0.50  % (14116)Time elapsed: 0.105 s
% 0.21/0.50  % (14116)------------------------------
% 0.21/0.50  % (14116)------------------------------
% 0.21/0.50  % (14096)Refutation not found, incomplete strategy% (14096)------------------------------
% 0.21/0.50  % (14096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14096)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (14096)Memory used [KB]: 10618
% 0.21/0.50  % (14096)Time elapsed: 0.105 s
% 0.21/0.50  % (14096)------------------------------
% 0.21/0.50  % (14096)------------------------------
% 0.21/0.50  % (14111)Refutation not found, incomplete strategy% (14111)------------------------------
% 0.21/0.50  % (14111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14109)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (14105)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (14111)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (14111)Memory used [KB]: 10618
% 0.21/0.50  % (14111)Time elapsed: 0.110 s
% 0.21/0.50  % (14111)------------------------------
% 0.21/0.50  % (14111)------------------------------
% 0.21/0.50  % (14095)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (14109)Refutation not found, incomplete strategy% (14109)------------------------------
% 0.21/0.51  % (14109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14102)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (14105)Refutation not found, incomplete strategy% (14105)------------------------------
% 0.21/0.51  % (14105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14105)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (14105)Memory used [KB]: 10618
% 0.21/0.51  % (14105)Time elapsed: 0.104 s
% 0.21/0.51  % (14105)------------------------------
% 0.21/0.51  % (14105)------------------------------
% 0.21/0.51  % (14119)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (14102)Refutation not found, incomplete strategy% (14102)------------------------------
% 0.21/0.51  % (14102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14102)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (14102)Memory used [KB]: 10618
% 0.21/0.51  % (14102)Time elapsed: 0.117 s
% 0.21/0.51  % (14102)------------------------------
% 0.21/0.51  % (14102)------------------------------
% 0.21/0.51  % (14109)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (14109)Memory used [KB]: 6140
% 0.21/0.51  % (14109)Time elapsed: 0.003 s
% 0.21/0.51  % (14109)------------------------------
% 0.21/0.51  % (14109)------------------------------
% 0.21/0.51  % (14120)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (14120)Refutation not found, incomplete strategy% (14120)------------------------------
% 0.21/0.51  % (14120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14120)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (14120)Memory used [KB]: 10746
% 0.21/0.51  % (14120)Time elapsed: 0.117 s
% 0.21/0.51  % (14120)------------------------------
% 0.21/0.51  % (14120)------------------------------
% 0.21/0.51  % (14118)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (14123)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (14110)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (14123)Refutation not found, incomplete strategy% (14123)------------------------------
% 0.21/0.51  % (14123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14123)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (14123)Memory used [KB]: 1791
% 0.21/0.51  % (14123)Time elapsed: 0.117 s
% 0.21/0.51  % (14123)------------------------------
% 0.21/0.51  % (14123)------------------------------
% 0.21/0.51  % (14112)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (14114)Refutation not found, incomplete strategy% (14114)------------------------------
% 0.21/0.51  % (14114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14114)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (14114)Memory used [KB]: 10618
% 0.21/0.51  % (14114)Time elapsed: 0.100 s
% 0.21/0.51  % (14114)------------------------------
% 0.21/0.51  % (14114)------------------------------
% 0.21/0.51  % (14121)Refutation not found, incomplete strategy% (14121)------------------------------
% 0.21/0.51  % (14121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14118)Refutation not found, incomplete strategy% (14118)------------------------------
% 0.21/0.51  % (14118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14118)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14118)Memory used [KB]: 6268
% 0.21/0.52  % (14118)Time elapsed: 0.120 s
% 0.21/0.52  % (14118)------------------------------
% 0.21/0.52  % (14118)------------------------------
% 0.21/0.52  % (14108)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (14110)# SZS output start Saturation.
% 0.21/0.52  tff(u159,axiom,
% 0.21/0.52      (![X1, X0] : (((k1_xboole_0 != k4_xboole_0(X0,X1)) | r1_tarski(X0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u158,axiom,
% 0.21/0.52      (![X0] : ((k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0)))).
% 0.21/0.52  
% 0.21/0.52  tff(u157,axiom,
% 0.21/0.52      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.21/0.52  
% 0.21/0.52  tff(u156,axiom,
% 0.21/0.52      (![X0] : ((k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u155,axiom,
% 0.21/0.52      (![X0] : ((k1_xboole_0 = k4_xboole_0(X0,X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u154,negated_conjecture,
% 0.21/0.52      ((~v1_xboole_0(sK1)) | (![X3] : ((k1_xboole_0 = k4_xboole_0(sK1,X3)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u153,negated_conjecture,
% 0.21/0.52      ((~(k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | (k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)))).
% 0.21/0.52  
% 0.21/0.52  tff(u152,axiom,
% 0.21/0.52      (![X1, X0] : ((k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u151,negated_conjecture,
% 0.21/0.52      ((~(k1_xboole_0 = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1)))) | (k1_xboole_0 = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u150,negated_conjecture,
% 0.21/0.52      ((~(sK0 = k3_tarski(k1_xboole_0))) | (sK0 = k3_tarski(k1_xboole_0)))).
% 0.21/0.52  
% 0.21/0.52  tff(u149,axiom,
% 0.21/0.52      (![X1, X0] : ((~v1_xboole_0(X0) | r1_tarski(X0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u148,axiom,
% 0.21/0.52      (![X1, X0] : ((~v1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1))) | v1_xboole_0(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u147,axiom,
% 0.21/0.52      ((~v1_xboole_0(k1_xboole_0)) | v1_xboole_0(k1_xboole_0))).
% 0.21/0.52  
% 0.21/0.52  tff(u146,negated_conjecture,
% 0.21/0.52      ((~v1_xboole_0(sK1)) | v1_xboole_0(sK1))).
% 0.21/0.52  
% 0.21/0.52  tff(u145,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u144,axiom,
% 0.21/0.52      (![X1, X0] : ((~r2_hidden(X1,X0) | ~v1_xboole_0(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u143,axiom,
% 0.21/0.52      (![X1, X0] : ((~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u142,axiom,
% 0.21/0.52      (![X0] : ((r2_hidden(sK2(X0),X0) | v1_xboole_0(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u141,axiom,
% 0.21/0.52      (![X1, X0] : ((r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u140,axiom,
% 0.21/0.52      (![X3, X2, X4] : ((~r1_tarski(X2,X4) | r2_hidden(sK3(X2,X3),X4) | r1_tarski(X2,X3))))).
% 0.21/0.52  
% 0.21/0.52  tff(u139,axiom,
% 0.21/0.52      (![X1, X0] : ((~r1_tarski(X0,X1) | r2_hidden(sK2(X0),X1) | v1_xboole_0(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u138,axiom,
% 0.21/0.52      (![X1, X0] : ((~r1_tarski(X0,X1) | (k1_xboole_0 = k4_xboole_0(X0,X1)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u137,axiom,
% 0.21/0.52      (![X0] : (r1_tarski(X0,X0)))).
% 0.21/0.52  
% 0.21/0.52  tff(u136,axiom,
% 0.21/0.52      ((~v1_xboole_0(k1_xboole_0)) | (![X0] : (r1_tarski(k1_xboole_0,X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u135,negated_conjecture,
% 0.21/0.52      ((~v1_xboole_0(sK1)) | (![X0] : (r1_tarski(sK1,X0))))).
% 0.21/0.52  
% 0.21/0.52  % (14110)# SZS output end Saturation.
% 0.21/0.52  % (14110)------------------------------
% 0.21/0.52  % (14110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14110)Termination reason: Satisfiable
% 0.21/0.52  
% 0.21/0.52  % (14110)Memory used [KB]: 10746
% 0.21/0.52  % (14110)Time elapsed: 0.121 s
% 0.21/0.52  % (14110)------------------------------
% 0.21/0.52  % (14110)------------------------------
% 0.21/0.52  % (14104)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (14093)Success in time 0.153 s
%------------------------------------------------------------------------------
