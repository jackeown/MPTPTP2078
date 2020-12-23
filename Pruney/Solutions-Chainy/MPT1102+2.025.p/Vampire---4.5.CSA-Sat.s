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
% DateTime   : Thu Dec  3 13:08:31 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    0
%              Number of atoms          :   24 (  24 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u69,negated_conjecture,(
    sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

tff(u68,negated_conjecture,
    ( ~ ( k1_xboole_0 != k4_xboole_0(k2_struct_0(sK0),u1_struct_0(sK0)) )
    | k1_xboole_0 != k4_xboole_0(k2_struct_0(sK0),u1_struct_0(sK0)) )).

tff(u67,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u66,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) )).

tff(u65,axiom,(
    ! [X1,X3,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X3,X1,X2)
      | k1_xboole_0 != k4_xboole_0(X1,X3) ) )).

tff(u64,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) )).

tff(u63,negated_conjecture,(
    k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) )).

tff(u62,negated_conjecture,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u61,axiom,(
    ! [X1,X3,X2] :
      ( ~ r1_tarski(X2,X1)
      | k4_xboole_0(X2,X3) = k7_subset_1(X1,X2,X3) ) )).

tff(u60,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) )).

tff(u59,negated_conjecture,(
    r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u58,axiom,(
    ! [X1,X0] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) )).

tff(u57,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u56,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u55,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u54,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:35:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (16675)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (16677)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (16683)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (16682)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (16674)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (16674)# SZS output start Saturation.
% 0.22/0.51  tff(u69,negated_conjecture,
% 0.22/0.51      (sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.22/0.51  
% 0.22/0.51  tff(u68,negated_conjecture,
% 0.22/0.51      ((~(k1_xboole_0 != k4_xboole_0(k2_struct_0(sK0),u1_struct_0(sK0)))) | (k1_xboole_0 != k4_xboole_0(k2_struct_0(sK0),u1_struct_0(sK0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u67,axiom,
% 0.22/0.51      (![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.22/0.51  
% 0.22/0.51  tff(u66,axiom,
% 0.22/0.51      (![X1, X0] : ((k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)))))).
% 0.22/0.51  
% 0.22/0.51  tff(u65,axiom,
% 0.22/0.51      (![X1, X3, X2] : (((k4_xboole_0(X1,X2) = k7_subset_1(X3,X1,X2)) | (k1_xboole_0 != k4_xboole_0(X1,X3)))))).
% 0.22/0.51  
% 0.22/0.51  tff(u64,axiom,
% 0.22/0.51      (![X0] : ((k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u63,negated_conjecture,
% 0.22/0.51      (k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)))).
% 0.22/0.51  
% 0.22/0.51  tff(u62,negated_conjecture,
% 0.22/0.51      (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u61,axiom,
% 0.22/0.51      (![X1, X3, X2] : ((~r1_tarski(X2,X1) | (k4_xboole_0(X2,X3) = k7_subset_1(X1,X2,X3)))))).
% 0.22/0.51  
% 0.22/0.51  tff(u60,axiom,
% 0.22/0.51      (![X1, X0] : ((~r1_tarski(X0,X1) | (k4_xboole_0(X0,X1) = k1_xboole_0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u59,negated_conjecture,
% 0.22/0.51      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.22/0.51  
% 0.22/0.51  tff(u58,axiom,
% 0.22/0.51      (![X1, X0] : ((r1_tarski(X0,X1) | (k4_xboole_0(X0,X1) != k1_xboole_0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u57,axiom,
% 0.22/0.51      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 0.22/0.51  
% 0.22/0.51  tff(u56,axiom,
% 0.22/0.51      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 0.22/0.51  
% 0.22/0.51  tff(u55,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.51  
% 0.22/0.51  tff(u54,axiom,
% 0.22/0.51      (![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))))).
% 0.22/0.51  
% 0.22/0.51  % (16674)# SZS output end Saturation.
% 0.22/0.51  % (16674)------------------------------
% 0.22/0.51  % (16674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (16674)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (16674)Memory used [KB]: 6140
% 0.22/0.51  % (16674)Time elapsed: 0.076 s
% 0.22/0.51  % (16674)------------------------------
% 0.22/0.51  % (16674)------------------------------
% 0.22/0.51  % (16678)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (16676)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (16671)Success in time 0.144 s
%------------------------------------------------------------------------------
