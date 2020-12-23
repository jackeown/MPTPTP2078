%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:31 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    0
%              Number of atoms          :   32 (  32 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u132,negated_conjecture,
    ( ~ ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )
    | sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

tff(u131,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u130,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u129,axiom,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 )).

tff(u128,negated_conjecture,
    ( u1_struct_0(sK0) != k2_xboole_0(sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

tff(u127,axiom,(
    ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) )).

tff(u126,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) )).

tff(u125,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK1,u1_struct_0(sK0))
    | k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) )).

tff(u124,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) )).

tff(u123,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) )).

tff(u122,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u121,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

tff(u120,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) )).

tff(u119,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) )).

tff(u118,negated_conjecture,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u117,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u116,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u115,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

% (23036)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
tff(u114,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u113,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u112,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:02:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (23024)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (23028)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (23032)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.47  % (23028)# SZS output start Saturation.
% 0.21/0.47  tff(u132,negated_conjecture,
% 0.21/0.47      ((~(sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))) | (sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))))).
% 0.21/0.47  
% 0.21/0.47  tff(u131,axiom,
% 0.21/0.47      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.21/0.47  
% 0.21/0.47  tff(u130,axiom,
% 0.21/0.47      (![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.21/0.47  
% 0.21/0.47  tff(u129,axiom,
% 0.21/0.47      (![X0] : ((k2_xboole_0(X0,X0) = X0)))).
% 0.21/0.47  
% 0.21/0.47  tff(u128,negated_conjecture,
% 0.21/0.47      ((~(u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0)))) | (u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u127,axiom,
% 0.21/0.47      (![X1, X0] : ((k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u126,axiom,
% 0.21/0.47      (![X0] : ((k1_xboole_0 = k4_xboole_0(X0,X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u125,negated_conjecture,
% 0.21/0.47      ((~(k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)))) | (k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u124,axiom,
% 0.21/0.47      (![X0] : ((k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u123,axiom,
% 0.21/0.47      (![X1, X0] : ((k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u122,negated_conjecture,
% 0.21/0.47      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u121,axiom,
% 0.21/0.47      (![X1, X0] : ((k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1))))).
% 0.21/0.47  
% 0.21/0.47  tff(u120,axiom,
% 0.21/0.47      (![X1, X0] : ((~r1_tarski(X0,X1) | (k2_xboole_0(X0,X1) = X1))))).
% 0.21/0.47  
% 0.21/0.47  tff(u119,axiom,
% 0.21/0.47      (![X1, X0] : ((~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u118,negated_conjecture,
% 0.21/0.47      ((~r1_tarski(sK1,u1_struct_0(sK0))) | r1_tarski(sK1,u1_struct_0(sK0)))).
% 0.21/0.47  
% 0.21/0.47  tff(u117,axiom,
% 0.21/0.47      (![X0] : (r1_tarski(X0,X0)))).
% 0.21/0.47  
% 0.21/0.47  tff(u116,axiom,
% 0.21/0.47      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u115,axiom,
% 0.21/0.47      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 0.21/0.47  
% 0.21/0.47  % (23036)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  tff(u114,negated_conjecture,
% 0.21/0.47      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u113,axiom,
% 0.21/0.47      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u112,negated_conjecture,
% 0.21/0.47      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.21/0.47  
% 0.21/0.47  % (23028)# SZS output end Saturation.
% 0.21/0.47  % (23028)------------------------------
% 0.21/0.47  % (23028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (23028)Termination reason: Satisfiable
% 0.21/0.47  
% 0.21/0.47  % (23028)Memory used [KB]: 6140
% 0.21/0.47  % (23028)Time elapsed: 0.053 s
% 0.21/0.47  % (23028)------------------------------
% 0.21/0.47  % (23028)------------------------------
% 0.21/0.48  % (23037)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (23021)Success in time 0.114 s
%------------------------------------------------------------------------------
