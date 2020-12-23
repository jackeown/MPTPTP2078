%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:48 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    0
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u106,negated_conjecture,
    ( ~ ( sK1 != k2_struct_0(sK0) )
    | sK1 != k2_struct_0(sK0) )).

tff(u105,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) )).

tff(u104,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u103,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u102,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u101,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2) )).

tff(u100,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u99,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u98,negated_conjecture,
    ( u1_struct_0(sK0) != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u97,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) )).

tff(u96,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u95,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) )).

tff(u94,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u93,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u92,axiom,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) ) )).

tff(u91,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:47:53 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.48  % (17353)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (17366)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.50  % (17366)Refutation not found, incomplete strategy% (17366)------------------------------
% 0.21/0.50  % (17366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (17366)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (17366)Memory used [KB]: 10746
% 0.21/0.50  % (17366)Time elapsed: 0.080 s
% 0.21/0.50  % (17366)------------------------------
% 0.21/0.50  % (17366)------------------------------
% 0.21/0.52  % (17348)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (17349)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (17349)Refutation not found, incomplete strategy% (17349)------------------------------
% 0.21/0.53  % (17349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (17349)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (17349)Memory used [KB]: 10746
% 0.21/0.53  % (17349)Time elapsed: 0.117 s
% 0.21/0.53  % (17349)------------------------------
% 0.21/0.53  % (17349)------------------------------
% 0.21/0.53  % (17365)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (17354)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (17362)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.54  % (17362)# SZS output start Saturation.
% 0.21/0.54  tff(u106,negated_conjecture,
% 0.21/0.54      ((~(sK1 != k2_struct_0(sK0))) | (sK1 != k2_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u105,axiom,
% 0.21/0.54      (![X0] : ((k1_xboole_0 = k4_xboole_0(X0,X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u104,negated_conjecture,
% 0.21/0.54      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u103,negated_conjecture,
% 0.21/0.54      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u102,axiom,
% 0.21/0.54      (![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u101,axiom,
% 0.21/0.54      (![X1, X2] : ((k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u100,axiom,
% 0.21/0.54      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u99,negated_conjecture,
% 0.21/0.54      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u98,negated_conjecture,
% 0.21/0.54      ((~(u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))))) | (u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u97,negated_conjecture,
% 0.21/0.54      ((~(sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u96,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u95,axiom,
% 0.21/0.54      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u94,negated_conjecture,
% 0.21/0.54      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u93,axiom,
% 0.21/0.54      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u92,axiom,
% 0.21/0.54      (![X0] : ((~l1_struct_0(X0) | (u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u91,negated_conjecture,
% 0.21/0.54      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.21/0.54  
% 0.21/0.54  % (17362)# SZS output end Saturation.
% 0.21/0.54  % (17362)------------------------------
% 0.21/0.54  % (17362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17362)Termination reason: Satisfiable
% 0.21/0.54  
% 0.21/0.54  % (17362)Memory used [KB]: 10746
% 0.21/0.54  % (17362)Time elapsed: 0.124 s
% 0.21/0.54  % (17362)------------------------------
% 0.21/0.54  % (17362)------------------------------
% 0.21/0.54  % (17345)Success in time 0.175 s
%------------------------------------------------------------------------------
