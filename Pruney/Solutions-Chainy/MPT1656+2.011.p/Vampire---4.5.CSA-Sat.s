%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:10 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    0
%              Number of atoms          :   83 (  83 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u94,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u93,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X1,X0] :
        ( ~ m1_subset_1(sK3(X0,k4_waybel_0(sK0,sK1),X1),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,sK3(X0,k4_waybel_0(sK0,sK1),X1))
        | r2_lattice3(X0,k4_waybel_0(sK0,sK1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) ) )).

tff(u92,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X3,X2] :
        ( ~ m1_subset_1(sK4(X2,k4_waybel_0(sK0,sK1),X3),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,sK4(X2,k4_waybel_0(sK0,sK1),X3))
        | r1_lattice3(X2,k4_waybel_0(sK0,sK1),X3)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ l1_orders_2(X2) ) )).

tff(u91,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u90,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u89,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u88,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u87,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK1,sK2)
    | ~ r1_lattice3(sK0,sK1,sK2) )).

tff(u86,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u85,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_lattice3(X0,X2,X3)
      | r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u84,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2) )).

tff(u83,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X0] :
        ( ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,X0) ) )).

tff(u82,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u81,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u80,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u79,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u78,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X0] :
        ( r1_orders_2(sK0,sK2,sK3(sK0,k4_waybel_0(sK0,sK1),X0))
        | r2_lattice3(sK0,k4_waybel_0(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u77,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X0] :
        ( r1_orders_2(sK0,sK2,sK4(sK0,k4_waybel_0(sK0,sK1),X0))
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u76,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u75,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_lattice3(X0,X2,X3)
      | r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u74,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X0] :
        ( ~ r1_tarski(X0,k4_waybel_0(sK0,sK1))
        | r1_lattice3(sK0,X0,sK2) ) )).

tff(u73,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u72,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u71,negated_conjecture,(
    v4_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (11963)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.20/0.46  % (11976)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.47  % (11976)Refutation not found, incomplete strategy% (11976)------------------------------
% 0.20/0.47  % (11976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (11976)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (11976)Memory used [KB]: 5373
% 0.20/0.47  % (11976)Time elapsed: 0.006 s
% 0.20/0.47  % (11976)------------------------------
% 0.20/0.47  % (11976)------------------------------
% 0.20/0.47  % (11972)WARNING: option uwaf not known.
% 0.20/0.47  % (11968)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.47  % (11972)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.20/0.48  % (11966)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.48  % (11975)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.48  % (11964)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.20/0.49  % (11967)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.49  % (11974)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.20/0.49  % (11970)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (11978)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.20/0.49  % (11978)Refutation not found, incomplete strategy% (11978)------------------------------
% 0.20/0.49  % (11978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (11978)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (11978)Memory used [KB]: 5373
% 0.20/0.49  % (11978)Time elapsed: 0.089 s
% 0.20/0.49  % (11978)------------------------------
% 0.20/0.49  % (11978)------------------------------
% 0.20/0.49  % (11971)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.20/0.49  % (11982)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.20/0.50  % (11965)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.20/0.50  % (11980)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (11965)Refutation not found, incomplete strategy% (11965)------------------------------
% 0.20/0.50  % (11965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (11965)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (11965)Memory used [KB]: 9850
% 0.20/0.50  % (11965)Time elapsed: 0.081 s
% 0.20/0.50  % (11965)------------------------------
% 0.20/0.50  % (11965)------------------------------
% 0.20/0.50  % (11977)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.20/0.50  % (11977)Refutation not found, incomplete strategy% (11977)------------------------------
% 0.20/0.50  % (11977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (11977)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (11977)Memory used [KB]: 895
% 0.20/0.50  % (11977)Time elapsed: 0.100 s
% 0.20/0.50  % (11977)------------------------------
% 0.20/0.50  % (11977)------------------------------
% 0.20/0.50  % (11981)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.20/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.50  % (11981)# SZS output start Saturation.
% 0.20/0.50  tff(u94,negated_conjecture,
% 0.20/0.50      l1_orders_2(sK0)).
% 0.20/0.50  
% 0.20/0.50  tff(u93,negated_conjecture,
% 0.20/0.50      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X1, X0] : ((~m1_subset_1(sK3(X0,k4_waybel_0(sK0,sK1),X1),u1_struct_0(sK0)) | r1_orders_2(sK0,sK2,sK3(X0,k4_waybel_0(sK0,sK1),X1)) | r2_lattice3(X0,k4_waybel_0(sK0,sK1),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u92,negated_conjecture,
% 0.20/0.50      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X3, X2] : ((~m1_subset_1(sK4(X2,k4_waybel_0(sK0,sK1),X3),u1_struct_0(sK0)) | r1_orders_2(sK0,sK2,sK4(X2,k4_waybel_0(sK0,sK1),X3)) | r1_lattice3(X2,k4_waybel_0(sK0,sK1),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_orders_2(X2)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u91,negated_conjecture,
% 0.20/0.50      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.50  
% 0.20/0.50  tff(u90,negated_conjecture,
% 0.20/0.50      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.50  
% 0.20/0.50  tff(u89,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u88,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u87,negated_conjecture,
% 0.20/0.50      ((~~r1_lattice3(sK0,sK1,sK2)) | ~r1_lattice3(sK0,sK1,sK2))).
% 0.20/0.50  
% 0.20/0.50  tff(u86,axiom,
% 0.20/0.50      (![X1, X0, X2, X4] : ((~r1_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X2,X4) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u85,axiom,
% 0.20/0.50      (![X1, X3, X0, X2] : ((~r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u84,negated_conjecture,
% 0.20/0.50      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2))).
% 0.20/0.50  
% 0.20/0.50  tff(u83,negated_conjecture,
% 0.20/0.50      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X0] : ((~r2_hidden(X0,k4_waybel_0(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK2,X0)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u82,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((r2_hidden(sK3(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u81,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((r2_hidden(sK4(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u80,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((~r1_orders_2(X0,sK3(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u79,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK4(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u78,negated_conjecture,
% 0.20/0.50      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X0] : ((r1_orders_2(sK0,sK2,sK3(sK0,k4_waybel_0(sK0,sK1),X0)) | r2_lattice3(sK0,k4_waybel_0(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))))))).
% 0.20/0.50  
% 0.20/0.50  tff(u77,negated_conjecture,
% 0.20/0.50      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X0] : ((r1_orders_2(sK0,sK2,sK4(sK0,k4_waybel_0(sK0,sK1),X0)) | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))))))).
% 0.20/0.50  
% 0.20/0.50  tff(u76,axiom,
% 0.20/0.50      (![X1, X0, X2, X4] : ((~r2_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u75,axiom,
% 0.20/0.50      (![X1, X3, X0, X2] : ((~r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u74,negated_conjecture,
% 0.20/0.50      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X0] : ((~r1_tarski(X0,k4_waybel_0(sK0,sK1)) | r1_lattice3(sK0,X0,sK2)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u73,negated_conjecture,
% 0.20/0.50      ~v2_struct_0(sK0)).
% 0.20/0.50  
% 0.20/0.50  tff(u72,negated_conjecture,
% 0.20/0.50      v3_orders_2(sK0)).
% 0.20/0.50  
% 0.20/0.50  tff(u71,negated_conjecture,
% 0.20/0.50      v4_orders_2(sK0)).
% 0.20/0.50  
% 0.20/0.50  % (11981)# SZS output end Saturation.
% 0.20/0.50  % (11981)------------------------------
% 0.20/0.50  % (11981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (11981)Termination reason: Satisfiable
% 0.20/0.50  
% 0.20/0.50  % (11981)Memory used [KB]: 5373
% 0.20/0.50  % (11981)Time elapsed: 0.100 s
% 0.20/0.50  % (11981)------------------------------
% 0.20/0.50  % (11981)------------------------------
% 0.20/0.50  % (11969)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.20/0.50  % (11960)Success in time 0.149 s
%------------------------------------------------------------------------------
