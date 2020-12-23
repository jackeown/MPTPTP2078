%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:03 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   35 (  35 expanded)
%              Depth                    :    0
%              Number of atoms          :   90 (  90 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u111,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u110,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | sP2(X2,X1,X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) )).

tff(u109,negated_conjecture,(
    m1_subset_1(sK4,u1_struct_0(sK3)) )).

tff(u108,negated_conjecture,(
    m1_subset_1(sK5,u1_struct_0(sK3)) )).

tff(u107,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u106,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK7(X0,X1,X2),X2)
      | ~ sP2(X0,X1,X2) ) )).

tff(u105,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X0)
      | ~ sP2(X0,X1,X2) ) )).

tff(u104,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u103,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK7(X0,X1,X2),X1)
      | ~ sP2(X0,X1,X2) ) )).

tff(u102,negated_conjecture,(
    ~ r1_tarski(k6_waybel_0(sK3,sK5),k6_waybel_0(sK3,sK4)) )).

tff(u101,axiom,(
    ! [X1,X0,X2] :
      ( r1_tarski(sK7(X0,X1,k1_zfmisc_1(X2)),sK7(X0,X1,k1_zfmisc_1(X2)))
      | ~ sP2(X0,X1,k1_zfmisc_1(X2)) ) )).

tff(u100,negated_conjecture,(
    l1_orders_2(sK3) )).

tff(u99,negated_conjecture,(
    ! [X0] :
      ( ~ r1_lattice3(sK3,X0,sK4)
      | sP0(sK4,sK3,X0) ) )).

tff(u98,negated_conjecture,(
    ! [X0] :
      ( ~ r1_lattice3(sK3,X0,sK5)
      | r1_lattice3(sK3,X0,sK4) ) )).

tff(u97,negated_conjecture,(
    ! [X1] :
      ( ~ r1_lattice3(sK3,X1,sK5)
      | sP0(sK5,sK3,X1) ) )).

tff(u96,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X5,X7,sK6(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK6(X4,X5,X6),X5,X7) ) )).

tff(u95,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X6,X7,sK7(X4,X5,u1_struct_0(X6)))
      | ~ l1_orders_2(X6)
      | ~ sP2(X4,X5,u1_struct_0(X6))
      | sP0(sK7(X4,X5,u1_struct_0(X6)),X6,X7) ) )).

tff(u94,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,X0,sK6(X0,X1,X2))
      | sP0(X0,X1,X2) ) )).

tff(u93,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ r1_lattice3(X0,X3,X2)
      | r1_lattice3(X0,X3,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u92,negated_conjecture,(
    r1_orders_2(sK3,sK4,sK5) )).

tff(u91,negated_conjecture,(
    v4_orders_2(sK3) )).

tff(u90,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_lattice3(X0,X3,X1)
      | r2_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u89,negated_conjecture,(
    ! [X0] :
      ( ~ sP0(sK4,sK3,X0)
      | r1_lattice3(sK3,X0,sK4) ) )).

tff(u88,negated_conjecture,(
    ! [X1] :
      ( ~ sP0(sK5,sK3,X1)
      | r1_lattice3(sK3,X1,sK5) ) )).

tff(u87,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) )).

tff(u86,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK6(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r1_lattice3(X1,X3,sK6(X0,X1,X2)) ) )).

tff(u85,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK7(X0,X1,u1_struct_0(X2)),X2,X3)
      | ~ l1_orders_2(X2)
      | ~ sP2(X0,X1,u1_struct_0(X2))
      | r1_lattice3(X2,X3,sK7(X0,X1,u1_struct_0(X2))) ) )).

tff(u84,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r1_lattice3(X1,X0,X2) ) )).

tff(u83,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r1_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u82,negated_conjecture,(
    ! [X0] : sP1(X0,sK3,sK4) )).

tff(u81,negated_conjecture,(
    ! [X1] : sP1(X1,sK3,sK5) )).

tff(u80,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP1(X3,X1,sK6(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

tff(u79,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP1(X3,X2,sK7(X0,X1,u1_struct_0(X2)))
      | ~ sP2(X0,X1,u1_struct_0(X2))
      | ~ l1_orders_2(X2) ) )).

tff(u78,axiom,(
    ! [X1,X0] : ~ sP2(X0,X0,X1) )).

tff(u77,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP2(sK7(X0,X1,k1_zfmisc_1(X2)),X3,X2)
      | r1_tarski(X3,sK7(X0,X1,k1_zfmisc_1(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ sP2(X0,X1,k1_zfmisc_1(X2)) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (2982)WARNING: option uwaf not known.
% 0.21/0.44  % (2982)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.21/0.46  % (2972)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.46  % (2972)Refutation not found, incomplete strategy% (2972)------------------------------
% 0.21/0.46  % (2972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (2972)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (2972)Memory used [KB]: 5373
% 0.21/0.46  % (2972)Time elapsed: 0.053 s
% 0.21/0.46  % (2972)------------------------------
% 0.21/0.46  % (2972)------------------------------
% 0.21/0.46  % (2987)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.47  % (2987)Refutation not found, incomplete strategy% (2987)------------------------------
% 0.21/0.47  % (2987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (2987)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (2987)Memory used [KB]: 895
% 0.21/0.47  % (2987)Time elapsed: 0.063 s
% 0.21/0.47  % (2987)------------------------------
% 0.21/0.47  % (2987)------------------------------
% 0.21/0.48  % (2990)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (2973)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.48  % (2985)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.48  % (2976)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.48  % (2988)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.21/0.48  % (2988)Refutation not found, incomplete strategy% (2988)------------------------------
% 0.21/0.48  % (2988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (2988)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (2988)Memory used [KB]: 5373
% 0.21/0.48  % (2988)Time elapsed: 0.086 s
% 0.21/0.48  % (2988)------------------------------
% 0.21/0.48  % (2988)------------------------------
% 0.21/0.49  % (2974)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.49  % (2975)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.49  % (2986)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.49  % (2975)Refutation not found, incomplete strategy% (2975)------------------------------
% 0.21/0.49  % (2975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (2975)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (2975)Memory used [KB]: 9850
% 0.21/0.49  % (2975)Time elapsed: 0.084 s
% 0.21/0.49  % (2975)------------------------------
% 0.21/0.49  % (2975)------------------------------
% 0.21/0.49  % (2977)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.49  % (2977)Refutation not found, incomplete strategy% (2977)------------------------------
% 0.21/0.49  % (2977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (2977)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (2977)Memory used [KB]: 895
% 0.21/0.49  % (2977)Time elapsed: 0.092 s
% 0.21/0.49  % (2977)------------------------------
% 0.21/0.49  % (2977)------------------------------
% 0.21/0.49  % (2984)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.49  % (2980)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (2979)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (2979)# SZS output start Saturation.
% 0.21/0.49  tff(u111,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u110,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X0)) | sP2(X2,X1,X0) | r1_tarski(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u109,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK4,u1_struct_0(sK3))).
% 0.21/0.49  
% 0.21/0.49  tff(u108,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK5,u1_struct_0(sK3))).
% 0.21/0.49  
% 0.21/0.50  tff(u107,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u106,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((m1_subset_1(sK7(X0,X1,X2),X2) | ~sP2(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u105,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~r2_hidden(sK7(X0,X1,X2),X0) | ~sP2(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u104,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((r2_hidden(sK6(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u103,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((r2_hidden(sK7(X0,X1,X2),X1) | ~sP2(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u102,negated_conjecture,
% 0.21/0.50      ~r1_tarski(k6_waybel_0(sK3,sK5),k6_waybel_0(sK3,sK4))).
% 0.21/0.50  
% 0.21/0.50  tff(u101,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((r1_tarski(sK7(X0,X1,k1_zfmisc_1(X2)),sK7(X0,X1,k1_zfmisc_1(X2))) | ~sP2(X0,X1,k1_zfmisc_1(X2)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u100,negated_conjecture,
% 0.21/0.50      l1_orders_2(sK3)).
% 0.21/0.50  
% 0.21/0.50  tff(u99,negated_conjecture,
% 0.21/0.50      (![X0] : ((~r1_lattice3(sK3,X0,sK4) | sP0(sK4,sK3,X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u98,negated_conjecture,
% 0.21/0.50      (![X0] : ((~r1_lattice3(sK3,X0,sK5) | r1_lattice3(sK3,X0,sK4))))).
% 0.21/0.50  
% 0.21/0.50  tff(u97,negated_conjecture,
% 0.21/0.50      (![X1] : ((~r1_lattice3(sK3,X1,sK5) | sP0(sK5,sK3,X1))))).
% 0.21/0.50  
% 0.21/0.50  tff(u96,axiom,
% 0.21/0.50      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK6(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK6(X4,X5,X6),X5,X7))))).
% 0.21/0.50  
% 0.21/0.50  tff(u95,axiom,
% 0.21/0.50      (![X5, X7, X4, X6] : ((~r1_lattice3(X6,X7,sK7(X4,X5,u1_struct_0(X6))) | ~l1_orders_2(X6) | ~sP2(X4,X5,u1_struct_0(X6)) | sP0(sK7(X4,X5,u1_struct_0(X6)),X6,X7))))).
% 0.21/0.50  
% 0.21/0.50  tff(u94,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~r1_orders_2(X1,X0,sK6(X0,X1,X2)) | sP0(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u93,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,X3,X2) | r1_lattice3(X0,X3,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u92,negated_conjecture,
% 0.21/0.50      r1_orders_2(sK3,sK4,sK5)).
% 0.21/0.50  
% 0.21/0.50  tff(u91,negated_conjecture,
% 0.21/0.50      v4_orders_2(sK3)).
% 0.21/0.50  
% 0.21/0.50  tff(u90,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((~r2_lattice3(X0,X3,X1) | r2_lattice3(X0,X3,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u89,negated_conjecture,
% 0.21/0.50      (![X0] : ((~sP0(sK4,sK3,X0) | r1_lattice3(sK3,X0,sK4))))).
% 0.21/0.50  
% 0.21/0.50  tff(u88,negated_conjecture,
% 0.21/0.50      (![X1] : ((~sP0(sK5,sK3,X1) | r1_lattice3(sK3,X1,sK5))))).
% 0.21/0.50  
% 0.21/0.50  tff(u87,axiom,
% 0.21/0.50      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X0,X4))))).
% 0.21/0.50  
% 0.21/0.50  tff(u86,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((~sP0(sK6(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r1_lattice3(X1,X3,sK6(X0,X1,X2)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u85,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((~sP0(sK7(X0,X1,u1_struct_0(X2)),X2,X3) | ~l1_orders_2(X2) | ~sP2(X0,X1,u1_struct_0(X2)) | r1_lattice3(X2,X3,sK7(X0,X1,u1_struct_0(X2))))))).
% 0.21/0.50  
% 0.21/0.50  tff(u84,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r1_lattice3(X1,X0,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u83,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r1_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u82,negated_conjecture,
% 0.21/0.50      (![X0] : (sP1(X0,sK3,sK4)))).
% 0.21/0.50  
% 0.21/0.50  tff(u81,negated_conjecture,
% 0.21/0.50      (![X1] : (sP1(X1,sK3,sK5)))).
% 0.21/0.50  
% 0.21/0.50  tff(u80,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((sP1(X3,X1,sK6(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.21/0.50  
% 0.21/0.50  tff(u79,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((sP1(X3,X2,sK7(X0,X1,u1_struct_0(X2))) | ~sP2(X0,X1,u1_struct_0(X2)) | ~l1_orders_2(X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u78,axiom,
% 0.21/0.50      (![X1, X0] : (~sP2(X0,X0,X1)))).
% 0.21/0.50  
% 0.21/0.50  tff(u77,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((sP2(sK7(X0,X1,k1_zfmisc_1(X2)),X3,X2) | r1_tarski(X3,sK7(X0,X1,k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~sP2(X0,X1,k1_zfmisc_1(X2)))))).
% 0.21/0.50  
% 0.21/0.50  % (2979)# SZS output end Saturation.
% 0.21/0.50  % (2979)------------------------------
% 0.21/0.50  % (2979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (2979)Termination reason: Satisfiable
% 0.21/0.50  
% 0.21/0.50  % (2979)Memory used [KB]: 5373
% 0.21/0.50  % (2979)Time elapsed: 0.072 s
% 0.21/0.50  % (2979)------------------------------
% 0.21/0.50  % (2979)------------------------------
% 0.21/0.50  % (2971)Success in time 0.143 s
%------------------------------------------------------------------------------
