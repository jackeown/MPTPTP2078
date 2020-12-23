%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:39 EST 2020

% Result     : CounterSatisfiable 1.49s
% Output     : Saturation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   61 (  61 expanded)
%              Number of leaves         :   61 (  61 expanded)
%              Depth                    :    0
%              Number of atoms          :   87 (  87 expanded)
%              Number of equality atoms :   56 (  56 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u2410,negated_conjecture,
    ( ~ ( sK1 != k2_struct_0(sK0) )
    | sK1 != k2_struct_0(sK0) )).

tff(u2409,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u2408,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) )).

tff(u2407,axiom,(
    ! [X3,X2] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) )).

tff(u2406,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) )).

tff(u2405,axiom,(
    ! [X31,X30] : k4_xboole_0(X30,k4_xboole_0(X30,X31)) = k4_xboole_0(k4_xboole_0(X31,k4_xboole_0(X31,X30)),k1_xboole_0) )).

tff(u2404,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) )).

tff(u2403,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) )).

tff(u2402,axiom,(
    ! [X3,X2] : k4_xboole_0(X2,k4_xboole_0(X2,X3)) = k5_xboole_0(X2,k4_xboole_0(X2,X3)) )).

tff(u2401,axiom,(
    ! [X3,X2] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3)) )).

tff(u2400,axiom,(
    ! [X32,X33] : k4_xboole_0(X32,k4_xboole_0(X32,X33)) = k5_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X32)),k1_xboole_0) )).

tff(u2399,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

tff(u2398,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | ! [X3] : k4_xboole_0(X3,k4_xboole_0(X3,u1_struct_0(sK0))) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(X3,k4_xboole_0(X3,u1_struct_0(sK0))))) )).

tff(u2397,axiom,(
    ! [X5,X6] : k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X5)),k1_xboole_0) )).

tff(u2396,axiom,(
    ! [X18,X19] : k4_xboole_0(k4_xboole_0(X18,k4_xboole_0(X18,X19)),k1_xboole_0) = k5_xboole_0(k4_xboole_0(X19,k4_xboole_0(X19,X18)),k1_xboole_0) )).

tff(u2395,axiom,(
    ! [X22,X23,X24] : k7_subset_1(k4_xboole_0(X23,k4_xboole_0(X23,X22)),k4_xboole_0(X22,k4_xboole_0(X22,X23)),X24) = k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X23)),X24) )).

tff(u2394,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),sK1)
    | k4_xboole_0(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) )).

tff(u2393,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | ! [X0] : k4_xboole_0(u1_struct_0(sK0),X0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))) )).

tff(u2392,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X7] : k7_subset_1(u1_struct_0(sK0),sK1,X7) = k4_xboole_0(sK1,X7) )).

tff(u2391,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u2390,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) )).

tff(u2389,axiom,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3) )).

tff(u2388,axiom,(
    ! [X11,X10] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,X11),X10) )).

tff(u2387,axiom,(
    ! [X3,X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) )).

tff(u2386,axiom,(
    ! [X34,X35] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X34,k4_xboole_0(X34,X35)),k4_xboole_0(X35,k4_xboole_0(X35,X34))) )).

tff(u2385,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK1,u1_struct_0(sK0))
    | k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) )).

tff(u2384,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) )).

tff(u2383,axiom,(
    ! [X20,X19] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(X20,k4_xboole_0(X20,X19)),k4_xboole_0(X19,k4_xboole_0(X19,X20))) )).

tff(u2382,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u2381,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u2380,axiom,(
    ! [X5,X6] : k1_xboole_0 = k7_subset_1(X5,k1_xboole_0,X6) )).

tff(u2379,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u2378,axiom,(
    ! [X3,X2,X4] : k7_subset_1(X2,k4_xboole_0(X2,X3),X4) = k4_xboole_0(k4_xboole_0(X2,X3),X4) )).

tff(u2377,axiom,(
    ! [X1,X0,X2] : k7_subset_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) )).

tff(u2376,negated_conjecture,
    ( u1_struct_0(sK0) != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u2375,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

tff(u2374,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) )).

tff(u2373,negated_conjecture,
    ( sK1 != k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | sK1 = k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

tff(u2372,negated_conjecture,
    ( sK1 != k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

tff(u2371,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) )).

tff(u2370,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) )).

tff(u2369,axiom,(
    ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) )).

tff(u2368,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u2367,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) )).

tff(u2366,axiom,(
    ! [X7,X6] : r1_tarski(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6) )).

tff(u2365,axiom,(
    ! [X23,X24] : r1_tarski(k4_xboole_0(X23,k4_xboole_0(X23,X24)),k4_xboole_0(X24,k4_xboole_0(X24,X23))) )).

tff(u2364,negated_conjecture,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u2363,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u2362,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u2361,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) )).

tff(u2360,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u2359,axiom,(
    ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) )).

tff(u2358,axiom,(
    ! [X5,X4] : m1_subset_1(k4_xboole_0(X5,k4_xboole_0(X5,X4)),k1_zfmisc_1(X4)) )).

tff(u2357,axiom,(
    ! [X22,X21] : m1_subset_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k1_zfmisc_1(k4_xboole_0(X22,k4_xboole_0(X22,X21)))) )).

tff(u2356,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

tff(u2355,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u2354,axiom,(
    ! [X5,X6] :
      ( ~ l1_struct_0(X5)
      | k4_xboole_0(X6,k4_xboole_0(X6,u1_struct_0(X5))) = k7_subset_1(u1_struct_0(X5),k2_struct_0(X5),k7_subset_1(u1_struct_0(X5),k2_struct_0(X5),k4_xboole_0(X6,k4_xboole_0(X6,u1_struct_0(X5))))) ) )).

tff(u2353,axiom,(
    ! [X3] :
      ( ~ l1_struct_0(X3)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X3),k2_struct_0(X3),k7_subset_1(u1_struct_0(X3),k2_struct_0(X3),k1_xboole_0)) ) )).

tff(u2352,axiom,(
    ! [X1,X2] :
      ( ~ l1_struct_0(X1)
      | k4_xboole_0(u1_struct_0(X1),X2) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k4_xboole_0(u1_struct_0(X1),X2))) ) )).

tff(u2351,axiom,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) ) )).

tff(u2350,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:39:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.51  % (3507)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (3499)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (3494)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (3515)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.52  % (3486)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (3493)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (3502)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (3488)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.53  % (3503)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.33/0.54  % (3489)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.33/0.54  % (3506)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.33/0.54  % (3512)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.33/0.54  % (3494)Refutation not found, incomplete strategy% (3494)------------------------------
% 1.33/0.54  % (3494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (3487)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.33/0.54  % (3491)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.33/0.54  % (3508)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.33/0.54  % (3486)Refutation not found, incomplete strategy% (3486)------------------------------
% 1.33/0.54  % (3486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (3494)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (3494)Memory used [KB]: 10746
% 1.33/0.54  % (3494)Time elapsed: 0.131 s
% 1.33/0.54  % (3494)------------------------------
% 1.33/0.54  % (3494)------------------------------
% 1.33/0.54  % (3511)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.33/0.54  % (3512)Refutation not found, incomplete strategy% (3512)------------------------------
% 1.33/0.54  % (3512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (3486)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (3486)Memory used [KB]: 1663
% 1.33/0.54  % (3486)Time elapsed: 0.132 s
% 1.33/0.54  % (3486)------------------------------
% 1.33/0.54  % (3486)------------------------------
% 1.33/0.54  % (3500)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.33/0.54  % (3501)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.33/0.54  % (3501)Refutation not found, incomplete strategy% (3501)------------------------------
% 1.33/0.54  % (3501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (3501)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (3501)Memory used [KB]: 6140
% 1.33/0.54  % (3501)Time elapsed: 0.001 s
% 1.33/0.54  % (3501)------------------------------
% 1.33/0.54  % (3501)------------------------------
% 1.33/0.54  % (3511)Refutation not found, incomplete strategy% (3511)------------------------------
% 1.33/0.54  % (3511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (3497)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.33/0.54  % (3495)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.33/0.55  % (3497)Refutation not found, incomplete strategy% (3497)------------------------------
% 1.33/0.55  % (3497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (3497)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (3497)Memory used [KB]: 10618
% 1.33/0.55  % (3497)Time elapsed: 0.152 s
% 1.33/0.55  % (3497)------------------------------
% 1.33/0.55  % (3497)------------------------------
% 1.33/0.55  % (3504)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.33/0.55  % (3490)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.33/0.55  % (3496)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.33/0.55  % (3490)Refutation not found, incomplete strategy% (3490)------------------------------
% 1.33/0.55  % (3490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (3490)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (3490)Memory used [KB]: 6268
% 1.33/0.55  % (3490)Time elapsed: 0.146 s
% 1.33/0.55  % (3490)------------------------------
% 1.33/0.55  % (3490)------------------------------
% 1.33/0.55  % (3496)Refutation not found, incomplete strategy% (3496)------------------------------
% 1.33/0.55  % (3496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (3503)Refutation not found, incomplete strategy% (3503)------------------------------
% 1.49/0.55  % (3503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (3503)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (3503)Memory used [KB]: 10618
% 1.49/0.55  % (3503)Time elapsed: 0.134 s
% 1.49/0.55  % (3503)------------------------------
% 1.49/0.55  % (3503)------------------------------
% 1.49/0.55  % (3488)Refutation not found, incomplete strategy% (3488)------------------------------
% 1.49/0.55  % (3488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (3488)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (3488)Memory used [KB]: 10746
% 1.49/0.55  % (3488)Time elapsed: 0.141 s
% 1.49/0.55  % (3488)------------------------------
% 1.49/0.55  % (3488)------------------------------
% 1.49/0.55  % (3512)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (3512)Memory used [KB]: 10746
% 1.49/0.55  % (3512)Time elapsed: 0.130 s
% 1.49/0.55  % (3512)------------------------------
% 1.49/0.55  % (3512)------------------------------
% 1.49/0.55  % (3514)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.49/0.55  % (3510)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.49/0.55  % (3508)Refutation not found, incomplete strategy% (3508)------------------------------
% 1.49/0.55  % (3508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (3508)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (3508)Memory used [KB]: 10746
% 1.49/0.55  % (3508)Time elapsed: 0.115 s
% 1.49/0.55  % (3508)------------------------------
% 1.49/0.55  % (3508)------------------------------
% 1.49/0.56  % (3506)Refutation not found, incomplete strategy% (3506)------------------------------
% 1.49/0.56  % (3506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (3506)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (3506)Memory used [KB]: 10874
% 1.49/0.56  % (3506)Time elapsed: 0.137 s
% 1.49/0.56  % (3506)------------------------------
% 1.49/0.56  % (3506)------------------------------
% 1.49/0.56  % (3492)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.49/0.56  % (3505)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.49/0.56  % (3496)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (3496)Memory used [KB]: 10618
% 1.49/0.56  % (3496)Time elapsed: 0.148 s
% 1.49/0.56  % (3496)------------------------------
% 1.49/0.56  % (3496)------------------------------
% 1.49/0.56  % (3495)Refutation not found, incomplete strategy% (3495)------------------------------
% 1.49/0.56  % (3495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (3495)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (3495)Memory used [KB]: 10618
% 1.49/0.56  % (3495)Time elapsed: 0.145 s
% 1.49/0.56  % (3495)------------------------------
% 1.49/0.56  % (3495)------------------------------
% 1.49/0.56  % (3511)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (3511)Memory used [KB]: 6268
% 1.49/0.56  % (3511)Time elapsed: 0.141 s
% 1.49/0.56  % (3511)------------------------------
% 1.49/0.56  % (3511)------------------------------
% 1.49/0.56  % (3498)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.56  % (3493)Refutation not found, incomplete strategy% (3493)------------------------------
% 1.49/0.56  % (3493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (3493)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (3493)Memory used [KB]: 6652
% 1.49/0.57  % (3493)Time elapsed: 0.137 s
% 1.49/0.57  % (3493)------------------------------
% 1.49/0.57  % (3493)------------------------------
% 1.49/0.57  % (3509)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.49/0.57  % (3513)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.49/0.58  % (3507)Refutation not found, incomplete strategy% (3507)------------------------------
% 1.49/0.58  % (3507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.58  % (3507)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.58  
% 1.49/0.58  % (3507)Memory used [KB]: 2046
% 1.49/0.58  % (3507)Time elapsed: 0.169 s
% 1.49/0.58  % (3507)------------------------------
% 1.49/0.58  % (3507)------------------------------
% 1.49/0.59  % (3509)Refutation not found, incomplete strategy% (3509)------------------------------
% 1.49/0.59  % (3509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.59  % (3509)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.59  
% 1.49/0.59  % (3509)Memory used [KB]: 1791
% 1.49/0.59  % (3509)Time elapsed: 0.153 s
% 1.49/0.59  % (3509)------------------------------
% 1.49/0.59  % (3509)------------------------------
% 1.49/0.60  % SZS status CounterSatisfiable for theBenchmark
% 1.49/0.60  % (3502)# SZS output start Saturation.
% 1.49/0.60  tff(u2410,negated_conjecture,
% 1.49/0.60      ((~(sK1 != k2_struct_0(sK0))) | (sK1 != k2_struct_0(sK0)))).
% 1.49/0.60  
% 1.49/0.60  tff(u2409,axiom,
% 1.49/0.60      (![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0)))).
% 1.49/0.60  
% 1.49/0.60  tff(u2408,axiom,
% 1.49/0.60      (![X1, X0] : ((k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2407,axiom,
% 1.49/0.60      (![X3, X2] : ((k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2406,axiom,
% 1.49/0.60      (![X1, X0] : ((k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2405,axiom,
% 1.49/0.60      (![X31, X30] : ((k4_xboole_0(X30,k4_xboole_0(X30,X31)) = k4_xboole_0(k4_xboole_0(X31,k4_xboole_0(X31,X30)),k1_xboole_0))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2404,axiom,
% 1.49/0.60      (![X1, X0] : ((k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2403,axiom,
% 1.49/0.60      (![X1, X0] : ((k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2402,axiom,
% 1.49/0.60      (![X3, X2] : ((k4_xboole_0(X2,k4_xboole_0(X2,X3)) = k5_xboole_0(X2,k4_xboole_0(X2,X3)))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2401,axiom,
% 1.49/0.60      (![X3, X2] : ((k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3)))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2400,axiom,
% 1.49/0.60      (![X32, X33] : ((k4_xboole_0(X32,k4_xboole_0(X32,X33)) = k5_xboole_0(k4_xboole_0(X33,k4_xboole_0(X33,X32)),k1_xboole_0))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2399,axiom,
% 1.49/0.60      (![X1, X0] : ((k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2398,negated_conjecture,
% 1.49/0.60      ((~l1_struct_0(sK0)) | (![X3] : ((k4_xboole_0(X3,k4_xboole_0(X3,u1_struct_0(sK0))) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(X3,k4_xboole_0(X3,u1_struct_0(sK0)))))))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2397,axiom,
% 1.49/0.60      (![X5, X6] : ((k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X5)),k1_xboole_0))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2396,axiom,
% 1.49/0.60      (![X18, X19] : ((k4_xboole_0(k4_xboole_0(X18,k4_xboole_0(X18,X19)),k1_xboole_0) = k5_xboole_0(k4_xboole_0(X19,k4_xboole_0(X19,X18)),k1_xboole_0))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2395,axiom,
% 1.49/0.60      (![X22, X23, X24] : ((k7_subset_1(k4_xboole_0(X23,k4_xboole_0(X23,X22)),k4_xboole_0(X22,k4_xboole_0(X22,X23)),X24) = k4_xboole_0(k4_xboole_0(X22,k4_xboole_0(X22,X23)),X24))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2394,negated_conjecture,
% 1.49/0.60      ((~(k4_xboole_0(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1))) | (k4_xboole_0(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)))).
% 1.49/0.60  
% 1.49/0.60  tff(u2393,negated_conjecture,
% 1.49/0.60      ((~l1_struct_0(sK0)) | (![X0] : ((k4_xboole_0(u1_struct_0(sK0),X0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)))))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2392,negated_conjecture,
% 1.49/0.60      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X7] : ((k7_subset_1(u1_struct_0(sK0),sK1,X7) = k4_xboole_0(sK1,X7)))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2391,axiom,
% 1.49/0.60      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 1.49/0.60  
% 1.49/0.60  tff(u2390,axiom,
% 1.49/0.60      (![X0] : ((k1_xboole_0 = k4_xboole_0(X0,X0))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2389,axiom,
% 1.49/0.60      (![X3] : ((k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2388,axiom,
% 1.49/0.60      (![X11, X10] : ((k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,X11),X10))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2387,axiom,
% 1.49/0.60      (![X3, X2] : ((k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2386,axiom,
% 1.49/0.60      (![X34, X35] : ((k1_xboole_0 = k4_xboole_0(k4_xboole_0(X34,k4_xboole_0(X34,X35)),k4_xboole_0(X35,k4_xboole_0(X35,X34))))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2385,negated_conjecture,
% 1.49/0.60      ((~(k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)))) | (k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2384,axiom,
% 1.49/0.60      (![X0] : ((k1_xboole_0 = k5_xboole_0(X0,X0))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2383,axiom,
% 1.49/0.60      (![X20, X19] : ((k1_xboole_0 = k5_xboole_0(k4_xboole_0(X20,k4_xboole_0(X20,X19)),k4_xboole_0(X19,k4_xboole_0(X19,X20))))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2382,negated_conjecture,
% 1.49/0.60      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 1.49/0.60  
% 1.49/0.60  tff(u2381,negated_conjecture,
% 1.49/0.60      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 1.49/0.60  
% 1.49/0.60  tff(u2380,axiom,
% 1.49/0.60      (![X5, X6] : ((k1_xboole_0 = k7_subset_1(X5,k1_xboole_0,X6))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2379,axiom,
% 1.49/0.60      (![X0] : ((k2_subset_1(X0) = X0)))).
% 1.49/0.60  
% 1.49/0.60  tff(u2378,axiom,
% 1.49/0.60      (![X3, X2, X4] : ((k7_subset_1(X2,k4_xboole_0(X2,X3),X4) = k4_xboole_0(k4_xboole_0(X2,X3),X4))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2377,axiom,
% 1.49/0.60      (![X1, X0, X2] : ((k7_subset_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2376,negated_conjecture,
% 1.49/0.60      ((~(u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))))) | (u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2375,negated_conjecture,
% 1.49/0.60      ((~(sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0))) | (sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)))).
% 1.49/0.60  
% 1.49/0.60  tff(u2374,negated_conjecture,
% 1.49/0.60      ((~(sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))).
% 1.49/0.60  
% 1.49/0.60  tff(u2373,negated_conjecture,
% 1.49/0.60      ((~(sK1 = k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)))) | (sK1 = k5_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2372,negated_conjecture,
% 1.49/0.60      ((~(sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)))) | (sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2371,axiom,
% 1.49/0.60      (![X1, X0] : ((~r1_tarski(X0,X1) | (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2370,axiom,
% 1.49/0.60      (![X1, X0] : ((~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2369,axiom,
% 1.49/0.60      (![X1, X0] : (r1_tarski(k4_xboole_0(X0,X1),X0)))).
% 1.49/0.60  
% 1.49/0.60  tff(u2368,axiom,
% 1.49/0.60      (![X0] : (r1_tarski(X0,X0)))).
% 1.49/0.60  
% 1.49/0.60  tff(u2367,axiom,
% 1.49/0.60      (![X1] : (r1_tarski(k1_xboole_0,X1)))).
% 1.49/0.60  
% 1.49/0.60  tff(u2366,axiom,
% 1.49/0.60      (![X7, X6] : (r1_tarski(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6)))).
% 1.49/0.60  
% 1.49/0.60  tff(u2365,axiom,
% 1.49/0.60      (![X23, X24] : (r1_tarski(k4_xboole_0(X23,k4_xboole_0(X23,X24)),k4_xboole_0(X24,k4_xboole_0(X24,X23)))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2364,negated_conjecture,
% 1.49/0.60      ((~r1_tarski(sK1,u1_struct_0(sK0))) | r1_tarski(sK1,u1_struct_0(sK0)))).
% 1.49/0.60  
% 1.49/0.60  tff(u2363,axiom,
% 1.49/0.60      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2362,axiom,
% 1.49/0.60      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2361,axiom,
% 1.49/0.60      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2360,axiom,
% 1.49/0.60      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2359,axiom,
% 1.49/0.60      (![X1, X0] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2358,axiom,
% 1.49/0.60      (![X5, X4] : (m1_subset_1(k4_xboole_0(X5,k4_xboole_0(X5,X4)),k1_zfmisc_1(X4))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2357,axiom,
% 1.49/0.60      (![X22, X21] : (m1_subset_1(k4_xboole_0(X21,k4_xboole_0(X21,X22)),k1_zfmisc_1(k4_xboole_0(X22,k4_xboole_0(X22,X21))))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2356,axiom,
% 1.49/0.60      (![X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2355,negated_conjecture,
% 1.49/0.60      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2354,axiom,
% 1.49/0.60      (![X5, X6] : ((~l1_struct_0(X5) | (k4_xboole_0(X6,k4_xboole_0(X6,u1_struct_0(X5))) = k7_subset_1(u1_struct_0(X5),k2_struct_0(X5),k7_subset_1(u1_struct_0(X5),k2_struct_0(X5),k4_xboole_0(X6,k4_xboole_0(X6,u1_struct_0(X5)))))))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2353,axiom,
% 1.49/0.60      (![X3] : ((~l1_struct_0(X3) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X3),k2_struct_0(X3),k7_subset_1(u1_struct_0(X3),k2_struct_0(X3),k1_xboole_0))))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2352,axiom,
% 1.49/0.60      (![X1, X2] : ((~l1_struct_0(X1) | (k4_xboole_0(u1_struct_0(X1),X2) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k4_xboole_0(u1_struct_0(X1),X2)))))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2351,axiom,
% 1.49/0.60      (![X0] : ((~l1_struct_0(X0) | (u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)))))))).
% 1.49/0.60  
% 1.49/0.60  tff(u2350,negated_conjecture,
% 1.49/0.60      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 1.49/0.60  
% 1.49/0.60  % (3502)# SZS output end Saturation.
% 1.49/0.60  % (3502)------------------------------
% 1.49/0.60  % (3502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.60  % (3502)Termination reason: Satisfiable
% 1.49/0.60  
% 1.49/0.60  % (3502)Memory used [KB]: 11641
% 1.49/0.60  % (3502)Time elapsed: 0.189 s
% 1.49/0.60  % (3502)------------------------------
% 1.49/0.60  % (3502)------------------------------
% 1.49/0.60  % (3489)Refutation not found, incomplete strategy% (3489)------------------------------
% 1.49/0.60  % (3489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.60  % (3489)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.60  
% 1.49/0.60  % (3489)Memory used [KB]: 11385
% 1.49/0.60  % (3489)Time elapsed: 0.183 s
% 1.49/0.60  % (3489)------------------------------
% 1.49/0.60  % (3489)------------------------------
% 1.49/0.62  % (3491)Refutation not found, incomplete strategy% (3491)------------------------------
% 1.49/0.62  % (3491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.62  % (3491)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.62  
% 1.49/0.62  % (3491)Memory used [KB]: 6908
% 1.49/0.62  % (3491)Time elapsed: 0.200 s
% 1.49/0.62  % (3491)------------------------------
% 1.49/0.62  % (3491)------------------------------
% 1.49/0.62  % (3485)Success in time 0.254 s
%------------------------------------------------------------------------------
