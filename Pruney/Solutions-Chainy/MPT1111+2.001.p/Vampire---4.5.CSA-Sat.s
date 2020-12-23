%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:10 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    0
%              Number of atoms          :   42 (  42 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u134,negated_conjecture,
    ( ~ ( k1_xboole_0 != k1_struct_0(sK0) )
    | k1_xboole_0 != k1_struct_0(sK0) )).

tff(u133,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK1 )).

tff(u132,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(X0)
      | r1_tarski(X0,X1) ) )).

tff(u131,axiom,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) )).

tff(u130,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) )).

tff(u129,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) )).

tff(u128,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) )).

tff(u127,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) )).

tff(u126,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) )).

% (7088)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
tff(u125,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK2(X0,X1),X2)
      | r1_tarski(X0,X1) ) )).

tff(u124,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) )).

tff(u123,axiom,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ! [X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | k1_xboole_0 = X1 ) )).

tff(u122,negated_conjecture,
    ( ~ ~ r1_tarski(k1_struct_0(sK0),k1_xboole_0)
    | ~ r1_tarski(k1_struct_0(sK0),k1_xboole_0) )).

tff(u121,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u120,axiom,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ! [X0] : r1_tarski(k1_xboole_0,X0) )).

tff(u119,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK2(X0,X2),X1)
      | r1_tarski(X0,X2) ) )).

tff(u118,negated_conjecture,
    ( k1_xboole_0 != sK1
    | ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,k1_xboole_0) ) )).

tff(u117,negated_conjecture,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) )).

% (7094)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:31:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (7091)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (7083)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (7108)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.50  % (7108)Refutation not found, incomplete strategy% (7108)------------------------------
% 0.21/0.50  % (7108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7098)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (7090)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (7082)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (7108)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (7108)Memory used [KB]: 6268
% 0.21/0.51  % (7108)Time elapsed: 0.101 s
% 0.21/0.51  % (7108)------------------------------
% 0.21/0.51  % (7108)------------------------------
% 0.21/0.51  % (7099)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (7086)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (7084)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (7090)Refutation not found, incomplete strategy% (7090)------------------------------
% 0.21/0.51  % (7090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7090)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (7090)Memory used [KB]: 10618
% 0.21/0.51  % (7090)Time elapsed: 0.110 s
% 0.21/0.51  % (7090)------------------------------
% 0.21/0.51  % (7090)------------------------------
% 0.21/0.51  % (7107)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (7098)# SZS output start Saturation.
% 0.21/0.51  tff(u134,negated_conjecture,
% 0.21/0.51      ((~(k1_xboole_0 != k1_struct_0(sK0))) | (k1_xboole_0 != k1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  tff(u133,negated_conjecture,
% 0.21/0.51      ((~(k1_xboole_0 = sK1)) | (k1_xboole_0 = sK1))).
% 0.21/0.51  
% 0.21/0.51  tff(u132,axiom,
% 0.21/0.51      (![X1, X0] : ((~v1_xboole_0(X0) | r1_tarski(X0,X1))))).
% 0.21/0.51  
% 0.21/0.51  tff(u131,axiom,
% 0.21/0.51      ((~v1_xboole_0(k1_xboole_0)) | v1_xboole_0(k1_xboole_0))).
% 0.21/0.51  
% 0.21/0.51  tff(u130,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))))).
% 0.21/0.51  
% 0.21/0.51  tff(u129,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1))))).
% 0.21/0.51  
% 0.21/0.51  tff(u128,axiom,
% 0.21/0.51      (![X1, X0] : ((~r2_hidden(X1,X0) | ~v1_xboole_0(X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u127,axiom,
% 0.21/0.51      (![X1, X0] : ((~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1))))).
% 0.21/0.51  
% 0.21/0.51  tff(u126,axiom,
% 0.21/0.51      (![X1, X0] : ((r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1))))).
% 0.21/0.51  
% 0.21/0.51  % (7088)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  tff(u125,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~r1_tarski(X0,X2) | r2_hidden(sK2(X0,X1),X2) | r1_tarski(X0,X1))))).
% 0.21/0.51  
% 0.21/0.51  tff(u124,axiom,
% 0.21/0.51      (![X1, X0] : ((~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | (X0 = X1))))).
% 0.21/0.51  
% 0.21/0.51  tff(u123,axiom,
% 0.21/0.51      ((~v1_xboole_0(k1_xboole_0)) | (![X1] : ((~r1_tarski(X1,k1_xboole_0) | (k1_xboole_0 = X1)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u122,negated_conjecture,
% 0.21/0.51      ((~~r1_tarski(k1_struct_0(sK0),k1_xboole_0)) | ~r1_tarski(k1_struct_0(sK0),k1_xboole_0))).
% 0.21/0.51  
% 0.21/0.51  tff(u121,axiom,
% 0.21/0.51      (![X1] : (r1_tarski(X1,X1)))).
% 0.21/0.51  
% 0.21/0.51  tff(u120,axiom,
% 0.21/0.51      ((~v1_xboole_0(k1_xboole_0)) | (![X0] : (r1_tarski(k1_xboole_0,X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u119,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK2(X0,X2),X1) | r1_tarski(X0,X2))))).
% 0.21/0.51  
% 0.21/0.51  tff(u118,negated_conjecture,
% 0.21/0.51      ((~(k1_xboole_0 = sK1)) | (![X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,k1_xboole_0)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u117,negated_conjecture,
% 0.21/0.51      ((~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.51  
% 0.21/0.51  % (7094)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (7098)# SZS output end Saturation.
% 0.21/0.51  % (7098)------------------------------
% 0.21/0.51  % (7098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7098)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (7098)Memory used [KB]: 10746
% 0.21/0.51  % (7098)Time elapsed: 0.110 s
% 0.21/0.51  % (7098)------------------------------
% 0.21/0.51  % (7098)------------------------------
% 0.21/0.51  % (7078)Success in time 0.156 s
%------------------------------------------------------------------------------
