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
% DateTime   : Thu Dec  3 13:17:07 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    0
%              Number of atoms          :   98 (  98 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u106,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u105,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u104,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u103,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u102,negated_conjecture,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK3(X1,k3_waybel_0(sK0,sK1),X2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3(X1,k3_waybel_0(sK0,sK1),X2),X0)
        | r2_lattice3(X1,k3_waybel_0(sK0,sK1),X2)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ l1_orders_2(X1) ) )).

% (18895)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
tff(u101,negated_conjecture,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ! [X1,X0] :
        ( ~ m1_subset_1(sK3(X0,k3_waybel_0(sK0,sK1),X1),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3(X0,k3_waybel_0(sK0,sK1),X1),sK2)
        | r2_lattice3(X0,k3_waybel_0(sK0,sK1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) ) )).

tff(u100,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u99,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u98,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u97,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u96,negated_conjecture,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ! [X1,X0] :
        ( ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) )).

tff(u95,negated_conjecture,(
    r1_orders_2(sK0,sK2,sK2) )).

tff(u94,negated_conjecture,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ! [X0] :
        ( r1_orders_2(sK0,sK3(sK0,k3_waybel_0(sK0,sK1),X0),sK2)
        | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u93,negated_conjecture,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ! [X1,X0] :
        ( r1_orders_2(sK0,sK3(sK0,k3_waybel_0(sK0,sK1),X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X0)
        | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) )).

tff(u92,axiom,(
    ! [X1,X0,X2] :
      ( r1_orders_2(X0,sK3(X0,X1,X2),sK3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u91,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK1,sK2)
    | ~ r2_lattice3(sK0,sK1,sK2) )).

tff(u90,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_lattice3(X0,X3,X1)
      | r2_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u89,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u88,negated_conjecture,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2) )).

tff(u87,negated_conjecture,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ! [X0] :
        ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

% (18888)Refutation not found, incomplete strategy% (18888)------------------------------
% (18888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18888)Termination reason: Refutation not found, incomplete strategy

% (18888)Memory used [KB]: 9850
% (18888)Time elapsed: 0.124 s
% (18888)------------------------------
% (18888)------------------------------
% (18900)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% (18900)Refutation not found, incomplete strategy% (18900)------------------------------
% (18900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18900)Termination reason: Refutation not found, incomplete strategy

% (18900)Memory used [KB]: 895
% (18900)Time elapsed: 0.083 s
% (18900)------------------------------
% (18900)------------------------------
% (18894)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% (18892)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% (18901)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% (18896)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
tff(u86,negated_conjecture,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ! [X3,X2] :
        ( ~ r2_hidden(X3,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,X3,X2) ) )).

tff(u85,negated_conjecture,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ! [X0] :
        ( ~ r2_hidden(X0,k3_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK2) ) )).

tff(u84,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u83,negated_conjecture,(
    v4_orders_2(sK0) )).

tff(u82,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_lattice3(X0,X3,X2)
      | r1_lattice3(X0,X3,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:05:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (18890)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.48  % (18891)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.49  % (18898)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.49  % (18899)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.49  % (18893)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (18899)Refutation not found, incomplete strategy% (18899)------------------------------
% 0.22/0.50  % (18899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (18899)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (18899)Memory used [KB]: 5373
% 0.22/0.50  % (18899)Time elapsed: 0.084 s
% 0.22/0.50  % (18899)------------------------------
% 0.22/0.50  % (18899)------------------------------
% 0.22/0.51  % (18885)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.53  % (18887)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.22/0.53  % (18889)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.53  % (18888)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.54  % (18904)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.22/0.54  % (18895)WARNING: option uwaf not known.
% 0.22/0.54  % (18897)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.54  % (18904)# SZS output start Saturation.
% 0.22/0.54  tff(u106,negated_conjecture,
% 0.22/0.54      ~v2_struct_0(sK0)).
% 0.22/0.54  
% 0.22/0.54  tff(u105,negated_conjecture,
% 0.22/0.54      v3_orders_2(sK0)).
% 0.22/0.54  
% 0.22/0.54  tff(u104,negated_conjecture,
% 0.22/0.54      l1_orders_2(sK0)).
% 0.22/0.54  
% 0.22/0.54  tff(u103,axiom,
% 0.22/0.54      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u102,negated_conjecture,
% 0.22/0.54      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X1, X0, X2] : ((~m1_subset_1(sK3(X1,k3_waybel_0(sK0,sK1),X2),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(X1,k3_waybel_0(sK0,sK1),X2),X0) | r2_lattice3(X1,k3_waybel_0(sK0,sK1),X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1)))))).
% 0.22/0.54  
% 0.22/0.54  % (18895)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.22/0.54  tff(u101,negated_conjecture,
% 0.22/0.54      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X1, X0] : ((~m1_subset_1(sK3(X0,k3_waybel_0(sK0,sK1),X1),u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(X0,k3_waybel_0(sK0,sK1),X1),sK2) | r2_lattice3(X0,k3_waybel_0(sK0,sK1),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u100,negated_conjecture,
% 0.22/0.54      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.22/0.54  
% 0.22/0.54  tff(u99,negated_conjecture,
% 0.22/0.54      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.54  
% 0.22/0.54  tff(u98,axiom,
% 0.22/0.54      (![X1, X0, X2] : ((m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u97,axiom,
% 0.22/0.54      (![X1, X0, X2] : ((~r1_orders_2(X0,sK3(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u96,negated_conjecture,
% 0.22/0.54      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X1, X0] : ((~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X1) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0))))))).
% 0.22/0.54  
% 0.22/0.54  tff(u95,negated_conjecture,
% 0.22/0.54      r1_orders_2(sK0,sK2,sK2)).
% 0.22/0.54  
% 0.22/0.54  tff(u94,negated_conjecture,
% 0.22/0.54      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X0] : ((r1_orders_2(sK0,sK3(sK0,k3_waybel_0(sK0,sK1),X0),sK2) | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))))))).
% 0.22/0.54  
% 0.22/0.54  tff(u93,negated_conjecture,
% 0.22/0.54      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X1, X0] : ((r1_orders_2(sK0,sK3(sK0,k3_waybel_0(sK0,sK1),X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,X0) | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0))))))).
% 0.22/0.54  
% 0.22/0.54  tff(u92,axiom,
% 0.22/0.54      (![X1, X0, X2] : ((r1_orders_2(X0,sK3(X0,X1,X2),sK3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u91,negated_conjecture,
% 0.22/0.54      ((~~r2_lattice3(sK0,sK1,sK2)) | ~r2_lattice3(sK0,sK1,sK2))).
% 0.22/0.54  
% 0.22/0.54  tff(u90,axiom,
% 0.22/0.54      (![X1, X3, X0, X2] : ((~r2_lattice3(X0,X3,X1) | r2_lattice3(X0,X3,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u89,axiom,
% 0.22/0.54      (![X1, X0, X2, X4] : ((~r2_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u88,negated_conjecture,
% 0.22/0.54      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2))).
% 0.22/0.54  
% 0.22/0.54  tff(u87,negated_conjecture,
% 0.22/0.54      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X0] : ((r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X0) | ~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))))))).
% 0.22/0.54  
% 0.22/0.54  % (18888)Refutation not found, incomplete strategy% (18888)------------------------------
% 0.22/0.54  % (18888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18888)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18888)Memory used [KB]: 9850
% 0.22/0.54  % (18888)Time elapsed: 0.124 s
% 0.22/0.54  % (18888)------------------------------
% 0.22/0.54  % (18888)------------------------------
% 0.22/0.54  % (18900)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.54  % (18900)Refutation not found, incomplete strategy% (18900)------------------------------
% 0.22/0.54  % (18900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18900)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18900)Memory used [KB]: 895
% 0.22/0.54  % (18900)Time elapsed: 0.083 s
% 0.22/0.54  % (18900)------------------------------
% 0.22/0.54  % (18900)------------------------------
% 0.22/0.54  % (18894)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (18892)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.55  % (18901)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 1.54/0.55  % (18896)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 1.54/0.55  tff(u86,negated_conjecture,
% 1.54/0.55      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X3, X2] : ((~r2_hidden(X3,k3_waybel_0(sK0,sK1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_orders_2(sK0,X3,X2)))))).
% 1.54/0.55  
% 1.54/0.55  tff(u85,negated_conjecture,
% 1.54/0.55      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X0] : ((~r2_hidden(X0,k3_waybel_0(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,sK2)))))).
% 1.54/0.55  
% 1.54/0.55  tff(u84,axiom,
% 1.54/0.55      (![X1, X0, X2] : ((r2_hidden(sK3(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.54/0.55  
% 1.54/0.55  tff(u83,negated_conjecture,
% 1.54/0.55      v4_orders_2(sK0)).
% 1.54/0.55  
% 1.54/0.55  tff(u82,axiom,
% 1.54/0.55      (![X1, X3, X0, X2] : ((~r1_lattice3(X0,X3,X2) | r1_lattice3(X0,X3,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 1.54/0.55  
% 1.54/0.55  % (18904)# SZS output end Saturation.
% 1.54/0.55  % (18904)------------------------------
% 1.54/0.55  % (18904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.55  % (18904)Termination reason: Satisfiable
% 1.54/0.55  
% 1.54/0.55  % (18904)Memory used [KB]: 5373
% 1.54/0.55  % (18904)Time elapsed: 0.116 s
% 1.54/0.55  % (18904)------------------------------
% 1.54/0.55  % (18904)------------------------------
% 1.54/0.55  % (18884)Success in time 0.193 s
%------------------------------------------------------------------------------
