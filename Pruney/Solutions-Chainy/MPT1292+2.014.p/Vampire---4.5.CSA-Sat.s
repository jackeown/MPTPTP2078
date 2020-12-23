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
% DateTime   : Thu Dec  3 13:13:13 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u103,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK1 )).

tff(u102,axiom,
    ( k1_xboole_0 != k3_tarski(k1_xboole_0)
    | k1_xboole_0 = k3_tarski(k1_xboole_0) )).

tff(u101,negated_conjecture,
    ( k1_xboole_0 != u1_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) )).

tff(u100,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) )).

tff(u99,axiom,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) )).

tff(u98,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) )).

tff(u97,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u96,axiom,(
    ! [X1,X0] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) )).

tff(u95,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),k1_xboole_0)
    | r1_tarski(u1_struct_0(sK0),k1_xboole_0) )).

tff(u94,axiom,
    ( k1_xboole_0 != k3_tarski(k1_xboole_0)
    | ! [X0] :
        ( ~ m1_setfam_1(k1_xboole_0,X0)
        | r1_tarski(X0,k1_xboole_0) ) )).

tff(u93,axiom,(
    ! [X3,X2] :
      ( ~ m1_setfam_1(X2,X3)
      | k3_tarski(X2) = X3
      | ~ r1_tarski(k3_tarski(X2),X3) ) )).

tff(u92,negated_conjecture,
    ( ~ m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))
    | m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) )).

tff(u91,negated_conjecture,
    ( ~ m1_setfam_1(k1_xboole_0,k1_xboole_0)
    | m1_setfam_1(k1_xboole_0,k1_xboole_0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (7232)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.47  % (7232)Refutation not found, incomplete strategy% (7232)------------------------------
% 0.21/0.47  % (7232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7240)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (7232)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7232)Memory used [KB]: 10618
% 0.21/0.49  % (7232)Time elapsed: 0.076 s
% 0.21/0.49  % (7232)------------------------------
% 0.21/0.49  % (7232)------------------------------
% 0.21/0.49  % (7227)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (7248)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.49  % (7248)Refutation not found, incomplete strategy% (7248)------------------------------
% 0.21/0.49  % (7248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7240)Refutation not found, incomplete strategy% (7240)------------------------------
% 0.21/0.49  % (7240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7240)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7240)Memory used [KB]: 6012
% 0.21/0.49  % (7240)Time elapsed: 0.096 s
% 0.21/0.49  % (7240)------------------------------
% 0.21/0.49  % (7240)------------------------------
% 0.21/0.49  % (7248)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7248)Memory used [KB]: 10618
% 0.21/0.49  % (7248)Time elapsed: 0.093 s
% 0.21/0.49  % (7248)------------------------------
% 0.21/0.49  % (7248)------------------------------
% 0.21/0.49  % (7249)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (7249)# SZS output start Saturation.
% 0.21/0.49  tff(u103,negated_conjecture,
% 0.21/0.49      ((~(k1_xboole_0 = sK1)) | (k1_xboole_0 = sK1))).
% 0.21/0.49  
% 0.21/0.49  tff(u102,axiom,
% 0.21/0.49      ((~(k1_xboole_0 = k3_tarski(k1_xboole_0))) | (k1_xboole_0 = k3_tarski(k1_xboole_0)))).
% 0.21/0.49  
% 0.21/0.49  tff(u101,negated_conjecture,
% 0.21/0.49      ((~(k1_xboole_0 = u1_struct_0(sK0))) | (k1_xboole_0 = u1_struct_0(sK0)))).
% 0.21/0.49  
% 0.21/0.49  tff(u100,axiom,
% 0.21/0.49      (![X1, X0] : ((~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | (X0 = X1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u99,axiom,
% 0.21/0.49      (![X0] : ((~r1_tarski(X0,k1_xboole_0) | (k1_xboole_0 = X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u98,axiom,
% 0.21/0.49      (![X0] : (r1_tarski(k1_xboole_0,X0)))).
% 0.21/0.49  
% 0.21/0.49  tff(u97,axiom,
% 0.21/0.49      (![X1] : (r1_tarski(X1,X1)))).
% 0.21/0.49  
% 0.21/0.49  tff(u96,axiom,
% 0.21/0.49      (![X1, X0] : ((r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u95,negated_conjecture,
% 0.21/0.49      ((~r1_tarski(u1_struct_0(sK0),k1_xboole_0)) | r1_tarski(u1_struct_0(sK0),k1_xboole_0))).
% 0.21/0.49  
% 0.21/0.49  tff(u94,axiom,
% 0.21/0.49      ((~(k1_xboole_0 = k3_tarski(k1_xboole_0))) | (![X0] : ((~m1_setfam_1(k1_xboole_0,X0) | r1_tarski(X0,k1_xboole_0)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u93,axiom,
% 0.21/0.49      (![X3, X2] : ((~m1_setfam_1(X2,X3) | (k3_tarski(X2) = X3) | ~r1_tarski(k3_tarski(X2),X3))))).
% 0.21/0.49  
% 0.21/0.49  tff(u92,negated_conjecture,
% 0.21/0.49      ((~m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))) | m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)))).
% 0.21/0.49  
% 0.21/0.49  tff(u91,negated_conjecture,
% 0.21/0.49      ((~m1_setfam_1(k1_xboole_0,k1_xboole_0)) | m1_setfam_1(k1_xboole_0,k1_xboole_0))).
% 0.21/0.49  
% 0.21/0.49  % (7249)# SZS output end Saturation.
% 0.21/0.49  % (7249)------------------------------
% 0.21/0.49  % (7249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7249)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (7249)Memory used [KB]: 10618
% 0.21/0.49  % (7249)Time elapsed: 0.048 s
% 0.21/0.49  % (7249)------------------------------
% 0.21/0.49  % (7249)------------------------------
% 0.21/0.50  % (7225)Success in time 0.139 s
%------------------------------------------------------------------------------
