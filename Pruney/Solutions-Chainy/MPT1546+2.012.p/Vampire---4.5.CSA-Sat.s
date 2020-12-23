%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:01 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    0
%              Number of atoms          :  108 ( 108 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u130,negated_conjecture,
    ( ~ ( sK1 != k13_lattice3(sK0,sK1,sK2) )
    | sK1 != k13_lattice3(sK0,sK1,sK2) )).

tff(u129,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(X1,sK3(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0) ) )).

tff(u128,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(X1,sK3(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ v3_orders_2(X0) ) )).

tff(u127,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(X2,sK3(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0) ) )).

tff(u126,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(X2,sK3(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ v3_orders_2(X0) ) )).

tff(u125,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) )).

tff(u124,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X3) ) )).

tff(u123,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X3) ) )).

tff(u122,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ v1_xboole_0(u1_struct_0(X1))
      | v2_struct_0(X1) ) )).

tff(u121,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u120,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u119,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0) ) )).

tff(u118,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ v3_orders_2(X0) ) )).

tff(u117,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u116,axiom,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) )).

tff(u115,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u114,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u113,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u112,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u111,axiom,(
    ! [X3,X5,X4] :
      ( ~ r1_orders_2(X4,X5,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ v3_orders_2(X4)
      | ~ l1_orders_2(X4)
      | ~ v1_xboole_0(u1_struct_0(X4)) ) )).

tff(u110,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK2,sK1) )).

tff(u109,axiom,(
    ! [X1,X0] :
      ( r1_orders_2(X0,X1,X1)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) )).

tff(u108,axiom,(
    ! [X1,X0,X2,X4] :
      ( r1_orders_2(X0,X2,X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v6_orders_2(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X4)
      | ~ r2_hidden(X2,X4)
      | r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0) ) )).

tff(u107,axiom,(
    ! [X1,X0,X2] :
      ( v6_orders_2(sK3(X0,X1,X2),X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0) ) )).

tff(u106,axiom,(
    ! [X1,X0,X2] :
      ( v6_orders_2(sK3(X0,X1,X2),X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ v3_orders_2(X0) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:41:44 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (16033)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.50  % (16043)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.50  % (16038)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  % (16043)Refutation not found, incomplete strategy% (16043)------------------------------
% 0.22/0.50  % (16043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (16043)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (16043)Memory used [KB]: 10490
% 0.22/0.50  % (16043)Time elapsed: 0.084 s
% 0.22/0.50  % (16043)------------------------------
% 0.22/0.50  % (16043)------------------------------
% 0.22/0.50  % (16037)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (16040)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (16049)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.51  % (16040)Refutation not found, incomplete strategy% (16040)------------------------------
% 0.22/0.51  % (16040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (16040)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (16040)Memory used [KB]: 6012
% 0.22/0.51  % (16040)Time elapsed: 0.060 s
% 0.22/0.51  % (16040)------------------------------
% 0.22/0.51  % (16040)------------------------------
% 0.22/0.51  % (16049)Refutation not found, incomplete strategy% (16049)------------------------------
% 0.22/0.51  % (16049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (16049)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (16049)Memory used [KB]: 1535
% 0.22/0.51  % (16049)Time elapsed: 0.092 s
% 0.22/0.51  % (16049)------------------------------
% 0.22/0.51  % (16049)------------------------------
% 0.22/0.51  % (16039)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (16041)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.51  % (16057)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.51  % (16035)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (16055)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.51  % (16056)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.51  % (16035)Refutation not found, incomplete strategy% (16035)------------------------------
% 0.22/0.51  % (16035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (16035)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (16035)Memory used [KB]: 10618
% 0.22/0.51  % (16035)Time elapsed: 0.104 s
% 0.22/0.51  % (16035)------------------------------
% 0.22/0.51  % (16035)------------------------------
% 0.22/0.51  % (16034)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.52  % (16045)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.52  % (16045)# SZS output start Saturation.
% 0.22/0.52  tff(u130,negated_conjecture,
% 0.22/0.52      ((~(sK1 != k13_lattice3(sK0,sK1,sK2))) | (sK1 != k13_lattice3(sK0,sK1,sK2)))).
% 0.22/0.52  
% 0.22/0.52  tff(u129,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((r2_hidden(X1,sK3(X0,X1,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u128,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((r2_hidden(X1,sK3(X0,X1,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X1) | ~v3_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u127,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((r2_hidden(X2,sK3(X0,X1,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u126,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((r2_hidden(X2,sK3(X0,X1,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X1) | ~v3_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u125,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2))))).
% 0.22/0.52  
% 0.22/0.52  tff(u124,axiom,
% 0.22/0.52      (![X1, X3, X0, X2] : ((~m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X3)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~v1_xboole_0(X3))))).
% 0.22/0.52  
% 0.22/0.52  tff(u123,axiom,
% 0.22/0.52      (![X1, X3, X0, X2] : ((~m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X3)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X1) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~v1_xboole_0(X3))))).
% 0.22/0.52  
% 0.22/0.52  tff(u122,axiom,
% 0.22/0.52      (![X1, X0] : ((~m1_subset_1(X0,u1_struct_0(X1)) | ~v3_orders_2(X1) | ~l1_orders_2(X1) | ~v1_xboole_0(u1_struct_0(X1)) | v2_struct_0(X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u121,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.22/0.52  
% 0.22/0.52  tff(u120,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.52  
% 0.22/0.52  tff(u119,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u118,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X1) | ~v3_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u117,negated_conjecture,
% 0.22/0.52      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.22/0.52  
% 0.22/0.52  tff(u116,axiom,
% 0.22/0.52      (![X0] : ((v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u115,negated_conjecture,
% 0.22/0.52      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.22/0.52  
% 0.22/0.52  tff(u114,axiom,
% 0.22/0.52      (![X0] : ((l1_struct_0(X0) | ~l1_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u113,negated_conjecture,
% 0.22/0.52      l1_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u112,negated_conjecture,
% 0.22/0.52      v3_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u111,axiom,
% 0.22/0.52      (![X3, X5, X4] : ((~r1_orders_2(X4,X5,X3) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~m1_subset_1(X3,u1_struct_0(X4)) | ~v3_orders_2(X4) | ~l1_orders_2(X4) | ~v1_xboole_0(u1_struct_0(X4)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u110,negated_conjecture,
% 0.22/0.52      ((~r1_orders_2(sK0,sK2,sK1)) | r1_orders_2(sK0,sK2,sK1))).
% 0.22/0.52  
% 0.22/0.52  tff(u109,axiom,
% 0.22/0.52      (![X1, X0] : ((r1_orders_2(X0,X1,X1) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u108,axiom,
% 0.22/0.52      (![X1, X0, X2, X4] : ((r1_orders_2(X0,X2,X1) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v6_orders_2(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~r2_hidden(X2,X4) | r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u107,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((v6_orders_2(sK3(X0,X1,X2),X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u106,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((v6_orders_2(sK3(X0,X1,X2),X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X1) | ~v3_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  % (16045)# SZS output end Saturation.
% 0.22/0.52  % (16045)------------------------------
% 0.22/0.52  % (16045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (16045)Termination reason: Satisfiable
% 0.22/0.52  
% 0.22/0.52  % (16045)Memory used [KB]: 10618
% 0.22/0.52  % (16045)Time elapsed: 0.107 s
% 0.22/0.52  % (16045)------------------------------
% 0.22/0.52  % (16045)------------------------------
% 0.22/0.52  % (16042)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.52  % (16046)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (16048)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.52  % (16047)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  % (16036)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.52  % (16036)Refutation not found, incomplete strategy% (16036)------------------------------
% 0.22/0.52  % (16036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (16036)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (16036)Memory used [KB]: 10618
% 0.22/0.52  % (16036)Time elapsed: 0.112 s
% 0.22/0.52  % (16036)------------------------------
% 0.22/0.52  % (16036)------------------------------
% 0.22/0.52  % (16030)Success in time 0.159 s
%------------------------------------------------------------------------------
