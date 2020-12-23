%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:50 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    0
%              Number of atoms          :   29 (  29 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u115,negated_conjecture,
    ( ~ ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u114,negated_conjecture,
    ( ~ ( k1_xboole_0 != k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)) )
    | k1_xboole_0 != k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)) )).

tff(u113,negated_conjecture,
    ( ~ ( sK1 != k2_struct_0(sK0) )
    | sK1 != k2_struct_0(sK0) )).

tff(u112,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u111,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X2] : k7_subset_1(u1_struct_0(sK0),sK1,X2) = k5_xboole_0(sK1,k3_xboole_0(sK1,X2)) )).

tff(u110,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

tff(u109,axiom,(
    ! [X0] : k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,k1_xboole_0) )).

tff(u108,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u107,axiom,(
    ! [X1,X0] : k7_subset_1(X0,k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) )).

tff(u106,axiom,(
    ! [X1,X0,X2] : k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0) )).

tff(u105,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) )).

tff(u104,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ) )).

tff(u103,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) )).

tff(u102,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

tff(u101,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u100,axiom,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k1_xboole_0)) ) )).

tff(u99,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (19147)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (19141)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (19142)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (19142)Refutation not found, incomplete strategy% (19142)------------------------------
% 0.20/0.51  % (19142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19142)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (19142)Memory used [KB]: 6140
% 0.20/0.51  % (19142)Time elapsed: 0.105 s
% 0.20/0.51  % (19142)------------------------------
% 0.20/0.51  % (19142)------------------------------
% 0.20/0.51  % (19147)Refutation not found, incomplete strategy% (19147)------------------------------
% 0.20/0.51  % (19147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19147)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (19147)Memory used [KB]: 10618
% 0.20/0.51  % (19147)Time elapsed: 0.102 s
% 0.20/0.51  % (19147)------------------------------
% 0.20/0.51  % (19147)------------------------------
% 0.20/0.51  % (19161)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (19149)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (19153)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (19153)Refutation not found, incomplete strategy% (19153)------------------------------
% 0.20/0.51  % (19153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19149)Refutation not found, incomplete strategy% (19149)------------------------------
% 0.20/0.51  % (19149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19149)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (19149)Memory used [KB]: 10618
% 0.20/0.51  % (19149)Time elapsed: 0.113 s
% 0.20/0.51  % (19149)------------------------------
% 0.20/0.51  % (19149)------------------------------
% 0.20/0.52  % (19153)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (19153)Memory used [KB]: 6140
% 0.20/0.52  % (19153)Time elapsed: 0.005 s
% 0.20/0.52  % (19153)------------------------------
% 0.20/0.52  % (19153)------------------------------
% 0.20/0.52  % (19161)Refutation not found, incomplete strategy% (19161)------------------------------
% 0.20/0.52  % (19161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (19161)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (19161)Memory used [KB]: 1663
% 0.20/0.52  % (19161)Time elapsed: 0.114 s
% 0.20/0.52  % (19161)------------------------------
% 0.20/0.52  % (19161)------------------------------
% 0.20/0.52  % (19143)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (19140)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (19143)Refutation not found, incomplete strategy% (19143)------------------------------
% 0.20/0.52  % (19143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (19143)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (19143)Memory used [KB]: 6268
% 0.20/0.52  % (19143)Time elapsed: 0.116 s
% 0.20/0.52  % (19143)------------------------------
% 0.20/0.52  % (19143)------------------------------
% 0.20/0.52  % (19138)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (19140)Refutation not found, incomplete strategy% (19140)------------------------------
% 0.20/0.52  % (19140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (19140)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (19140)Memory used [KB]: 10618
% 0.20/0.52  % (19140)Time elapsed: 0.127 s
% 0.20/0.52  % (19140)------------------------------
% 0.20/0.52  % (19140)------------------------------
% 0.20/0.52  % (19154)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (19138)Refutation not found, incomplete strategy% (19138)------------------------------
% 0.20/0.52  % (19138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (19138)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (19138)Memory used [KB]: 1663
% 0.20/0.52  % (19138)Time elapsed: 0.125 s
% 0.20/0.52  % (19138)------------------------------
% 0.20/0.52  % (19138)------------------------------
% 0.20/0.52  % (19160)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (19167)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.52  % (19154)# SZS output start Saturation.
% 0.20/0.52  tff(u115,negated_conjecture,
% 0.20/0.52      ((~(k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 0.20/0.52  
% 0.20/0.52  tff(u114,negated_conjecture,
% 0.20/0.52      ((~(k1_xboole_0 != k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)))) | (k1_xboole_0 != k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))))).
% 0.20/0.52  
% 0.20/0.52  tff(u113,negated_conjecture,
% 0.20/0.52      ((~(sK1 != k2_struct_0(sK0))) | (sK1 != k2_struct_0(sK0)))).
% 0.20/0.52  
% 0.20/0.52  tff(u112,axiom,
% 0.20/0.52      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.20/0.52  
% 0.20/0.52  tff(u111,negated_conjecture,
% 0.20/0.52      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X2] : ((k7_subset_1(u1_struct_0(sK0),sK1,X2) = k5_xboole_0(sK1,k3_xboole_0(sK1,X2))))))).
% 0.20/0.52  
% 0.20/0.52  tff(u110,axiom,
% 0.20/0.52      (![X0] : ((k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u109,axiom,
% 0.20/0.52      (![X0] : ((k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,k1_xboole_0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u108,negated_conjecture,
% 0.20/0.52      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.20/0.52  
% 0.20/0.52  tff(u107,axiom,
% 0.20/0.52      (![X1, X0] : ((k7_subset_1(X0,k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)))))).
% 0.20/0.52  
% 0.20/0.52  tff(u106,axiom,
% 0.20/0.52      (![X1, X0, X2] : ((k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u105,negated_conjecture,
% 0.20/0.52      ((~(sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))).
% 0.20/0.52  
% 0.20/0.52  tff(u104,axiom,
% 0.20/0.52      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))))))).
% 0.20/0.52  
% 0.20/0.52  tff(u103,axiom,
% 0.20/0.52      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))))).
% 0.20/0.52  
% 0.20/0.52  tff(u102,axiom,
% 0.20/0.52      (![X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u101,negated_conjecture,
% 0.20/0.52      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u100,axiom,
% 0.20/0.52      (![X0] : ((~l1_struct_0(X0) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k1_xboole_0))))))).
% 0.20/0.52  
% 0.20/0.52  tff(u99,negated_conjecture,
% 0.20/0.52      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.20/0.52  
% 0.20/0.52  % (19154)# SZS output end Saturation.
% 0.20/0.52  % (19154)------------------------------
% 0.20/0.52  % (19154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (19154)Termination reason: Satisfiable
% 0.20/0.52  
% 0.20/0.52  % (19154)Memory used [KB]: 10746
% 0.20/0.52  % (19154)Time elapsed: 0.130 s
% 0.20/0.52  % (19154)------------------------------
% 0.20/0.52  % (19154)------------------------------
% 0.20/0.52  % (19160)Refutation not found, incomplete strategy% (19160)------------------------------
% 0.20/0.52  % (19160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (19160)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (19160)Memory used [KB]: 10618
% 0.20/0.52  % (19160)Time elapsed: 0.094 s
% 0.20/0.52  % (19160)------------------------------
% 0.20/0.52  % (19160)------------------------------
% 0.20/0.52  % (19139)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (19137)Success in time 0.166 s
%------------------------------------------------------------------------------
