%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:57 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    0
%              Number of atoms          :   48 (  48 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u147,negated_conjecture,(
    sK0 != sK2 )).

tff(u146,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u145,axiom,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 )).

tff(u144,negated_conjecture,
    ( k1_xboole_0 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) )).

tff(u143,axiom,(
    ! [X1,X0,X2] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) )).

tff(u142,negated_conjecture,
    ( k1_xboole_0 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,sK0,sK1) = k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) )).

tff(u141,axiom,(
    ! [X3,X2] :
      ( ~ v1_xboole_0(k3_xboole_0(X2,X3))
      | r1_xboole_0(X2,X3) ) )).

tff(u140,axiom,(
    v1_xboole_0(k1_xboole_0) )).

tff(u139,axiom,(
    ! [X1,X0] :
      ( v1_xboole_0(k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) )).

tff(u138,axiom,(
    ! [X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) )).

tff(u137,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) )).

tff(u136,axiom,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) )).

tff(u135,axiom,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) )).

tff(u134,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) )).

tff(u133,axiom,(
    ! [X0] :
      ( r2_hidden(sK4(X0,X0),X0)
      | r1_xboole_0(X0,X0) ) )).

tff(u132,axiom,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | v1_xboole_0(X0) ) )).

tff(u131,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X0)
      | ~ r2_hidden(X1,X0) ) )).

tff(u130,axiom,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | ~ v1_xboole_0(X0) ) )).

tff(u129,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))
      | ~ r1_xboole_0(X1,X2) ) )).

tff(u128,axiom,(
    ! [X1,X0] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) )).

tff(u127,axiom,(
    ! [X0] : r1_xboole_0(k5_xboole_0(X0,X0),X0) )).

tff(u126,axiom,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) )).

tff(u125,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | X0 = X1 ) )).

tff(u124,negated_conjecture,(
    ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) )).

tff(u123,negated_conjecture,(
    ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) )).

tff(u122,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 ) )).

tff(u121,axiom,(
    ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) )).

tff(u120,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )).

tff(u119,axiom,(
    ! [X1] : r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )).

tff(u118,axiom,(
    ! [X1,X0,X2] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )).

tff(u117,negated_conjecture,
    ( k1_xboole_0 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:35:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (24473)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (24485)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (24479)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (24489)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.51  % (24475)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (24479)Refutation not found, incomplete strategy% (24479)------------------------------
% 0.21/0.51  % (24479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24472)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (24489)Refutation not found, incomplete strategy% (24489)------------------------------
% 0.21/0.51  % (24489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24489)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24489)Memory used [KB]: 1791
% 0.21/0.51  % (24489)Time elapsed: 0.114 s
% 0.21/0.51  % (24489)------------------------------
% 0.21/0.51  % (24489)------------------------------
% 0.21/0.51  % (24481)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (24479)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24479)Memory used [KB]: 1791
% 0.21/0.52  % (24479)Time elapsed: 0.116 s
% 0.21/0.52  % (24479)------------------------------
% 0.21/0.52  % (24479)------------------------------
% 0.21/0.52  % (24470)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (24483)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (24481)Refutation not found, incomplete strategy% (24481)------------------------------
% 0.21/0.52  % (24481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24495)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (24497)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (24497)Refutation not found, incomplete strategy% (24497)------------------------------
% 0.21/0.52  % (24497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24497)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24497)Memory used [KB]: 6268
% 0.21/0.52  % (24497)Time elapsed: 0.120 s
% 0.21/0.52  % (24497)------------------------------
% 0.21/0.52  % (24497)------------------------------
% 0.21/0.52  % (24496)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (24488)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (24476)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (24494)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (24471)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (24498)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (24488)Refutation not found, incomplete strategy% (24488)------------------------------
% 0.21/0.54  % (24488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24488)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24488)Memory used [KB]: 1791
% 0.21/0.54  % (24488)Time elapsed: 0.132 s
% 0.21/0.54  % (24488)------------------------------
% 0.21/0.54  % (24488)------------------------------
% 0.21/0.54  % (24491)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (24471)Refutation not found, incomplete strategy% (24471)------------------------------
% 0.21/0.54  % (24471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24471)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24471)Memory used [KB]: 1663
% 0.21/0.54  % (24471)Time elapsed: 0.126 s
% 0.21/0.54  % (24471)------------------------------
% 0.21/0.54  % (24471)------------------------------
% 0.21/0.54  % (24474)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (24496)Refutation not found, incomplete strategy% (24496)------------------------------
% 0.21/0.54  % (24496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24481)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24481)Memory used [KB]: 6396
% 0.21/0.54  % (24481)Time elapsed: 0.111 s
% 0.21/0.54  % (24481)------------------------------
% 0.21/0.54  % (24481)------------------------------
% 0.21/0.54  % (24499)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (24496)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24496)Memory used [KB]: 6268
% 0.21/0.54  % (24496)Time elapsed: 0.121 s
% 0.21/0.54  % (24496)------------------------------
% 0.21/0.54  % (24496)------------------------------
% 0.21/0.54  % (24474)Refutation not found, incomplete strategy% (24474)------------------------------
% 0.21/0.54  % (24474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24474)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24474)Memory used [KB]: 1791
% 0.21/0.54  % (24474)Time elapsed: 0.127 s
% 0.21/0.54  % (24474)------------------------------
% 0.21/0.54  % (24474)------------------------------
% 0.21/0.54  % (24486)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (24495)Refutation not found, incomplete strategy% (24495)------------------------------
% 0.21/0.54  % (24495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24495)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24495)Memory used [KB]: 10618
% 0.21/0.54  % (24495)Time elapsed: 0.124 s
% 0.21/0.54  % (24495)------------------------------
% 0.21/0.54  % (24495)------------------------------
% 0.21/0.54  % (24484)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (24478)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (24494)Refutation not found, incomplete strategy% (24494)------------------------------
% 0.21/0.54  % (24494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24494)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24494)Memory used [KB]: 10746
% 0.21/0.54  % (24494)Time elapsed: 0.091 s
% 0.21/0.54  % (24494)------------------------------
% 0.21/0.54  % (24494)------------------------------
% 0.21/0.54  % (24484)Refutation not found, incomplete strategy% (24484)------------------------------
% 0.21/0.54  % (24484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24484)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24484)Memory used [KB]: 1663
% 0.21/0.54  % (24484)Time elapsed: 0.134 s
% 0.21/0.54  % (24484)------------------------------
% 0.21/0.54  % (24484)------------------------------
% 0.21/0.54  % (24482)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (24482)Refutation not found, incomplete strategy% (24482)------------------------------
% 0.21/0.54  % (24482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24482)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24482)Memory used [KB]: 10618
% 0.21/0.54  % (24482)Time elapsed: 0.140 s
% 0.21/0.54  % (24482)------------------------------
% 0.21/0.54  % (24482)------------------------------
% 0.21/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.54  % (24476)# SZS output start Saturation.
% 0.21/0.54  tff(u147,negated_conjecture,
% 0.21/0.54      (sK0 != sK2)).
% 0.21/0.54  
% 0.21/0.54  tff(u146,axiom,
% 0.21/0.54      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u145,axiom,
% 0.21/0.54      (![X0] : ((k3_xboole_0(X0,X0) = X0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u144,negated_conjecture,
% 0.21/0.54      ((~(k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | (k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u143,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u142,negated_conjecture,
% 0.21/0.54      ((~(k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | (![X0] : ((k6_enumset1(X0,X0,X0,X0,X0,X0,sK0,sK1) = k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u141,axiom,
% 0.21/0.54      (![X3, X2] : ((~v1_xboole_0(k3_xboole_0(X2,X3)) | r1_xboole_0(X2,X3))))).
% 0.21/0.54  
% 0.21/0.54  tff(u140,axiom,
% 0.21/0.54      v1_xboole_0(k1_xboole_0)).
% 0.21/0.54  
% 0.21/0.54  tff(u139,axiom,
% 0.21/0.54      (![X1, X0] : ((v1_xboole_0(k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u138,axiom,
% 0.21/0.54      (![X0, X2] : ((~r2_hidden(X2,X0) | ~v1_xboole_0(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u137,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u136,axiom,
% 0.21/0.54      (![X0] : (~r2_hidden(X0,k1_xboole_0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u135,axiom,
% 0.21/0.54      (![X0] : ((r2_hidden(sK3(X0),X0) | v1_xboole_0(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u134,axiom,
% 0.21/0.54      (![X1, X0] : ((r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u133,axiom,
% 0.21/0.54      (![X0] : ((r2_hidden(sK4(X0,X0),X0) | r1_xboole_0(X0,X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u132,axiom,
% 0.21/0.54      (![X0] : ((~r1_xboole_0(X0,X0) | v1_xboole_0(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u131,axiom,
% 0.21/0.54      (![X1, X0] : ((~r1_xboole_0(X0,X0) | ~r2_hidden(X1,X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u130,axiom,
% 0.21/0.54      (![X0] : ((r1_xboole_0(X0,X0) | ~v1_xboole_0(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u129,axiom,
% 0.21/0.54      (![X1, X2] : ((r1_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)) | ~r1_xboole_0(X1,X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u128,axiom,
% 0.21/0.54      (![X1, X0] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u127,axiom,
% 0.21/0.54      (![X0] : (r1_xboole_0(k5_xboole_0(X0,X0),X0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u126,axiom,
% 0.21/0.54      r1_xboole_0(k1_xboole_0,k1_xboole_0)).
% 0.21/0.54  
% 0.21/0.54  tff(u125,axiom,
% 0.21/0.54      (![X1, X0] : ((~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | (X0 = X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u124,negated_conjecture,
% 0.21/0.54      ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))).
% 0.21/0.54  
% 0.21/0.54  tff(u123,negated_conjecture,
% 0.21/0.54      ~r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))).
% 0.21/0.54  
% 0.21/0.54  tff(u122,axiom,
% 0.21/0.54      (![X1, X0] : ((~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | (k1_xboole_0 = X0) | (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u121,axiom,
% 0.21/0.54      (![X1, X0] : (r1_tarski(X0,k2_xboole_0(X0,X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u120,axiom,
% 0.21/0.54      (![X1] : (r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u119,axiom,
% 0.21/0.54      (![X1] : (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u118,axiom,
% 0.21/0.54      (![X1, X0, X2] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u117,negated_conjecture,
% 0.21/0.54      ((~(k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0))).
% 0.21/0.54  
% 0.21/0.54  % (24476)# SZS output end Saturation.
% 0.21/0.54  % (24476)------------------------------
% 0.21/0.54  % (24476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24476)Termination reason: Satisfiable
% 0.21/0.54  
% 0.21/0.54  % (24476)Memory used [KB]: 10746
% 0.21/0.54  % (24476)Time elapsed: 0.107 s
% 0.21/0.54  % (24476)------------------------------
% 0.21/0.54  % (24476)------------------------------
% 0.21/0.54  % (24492)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (24469)Success in time 0.177 s
%------------------------------------------------------------------------------
