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
% DateTime   : Thu Dec  3 13:17:06 EST 2020

% Result     : CounterSatisfiable 1.03s
% Output     : Saturation 1.03s
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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:29:14 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.39  ipcrm: permission denied for id (803176449)
% 0.14/0.39  ipcrm: permission denied for id (803209218)
% 0.14/0.40  ipcrm: permission denied for id (803340301)
% 0.22/0.41  ipcrm: permission denied for id (803373080)
% 0.22/0.42  ipcrm: permission denied for id (803405850)
% 0.22/0.42  ipcrm: permission denied for id (803438619)
% 0.22/0.43  ipcrm: permission denied for id (803536940)
% 0.22/0.43  ipcrm: permission denied for id (803569710)
% 0.22/0.44  ipcrm: permission denied for id (803635253)
% 0.22/0.44  ipcrm: permission denied for id (803668022)
% 0.22/0.44  ipcrm: permission denied for id (803700794)
% 0.22/0.45  ipcrm: permission denied for id (803766342)
% 0.22/0.47  ipcrm: permission denied for id (803897430)
% 0.22/0.48  ipcrm: permission denied for id (803962972)
% 0.22/0.49  ipcrm: permission denied for id (803995744)
% 0.22/0.51  ipcrm: permission denied for id (804225139)
% 0.22/0.52  ipcrm: permission denied for id (804323448)
% 0.22/0.52  ipcrm: permission denied for id (804356220)
% 0.67/0.62  % (1817)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 1.03/0.63  % (1823)WARNING: option uwaf not known.
% 1.03/0.64  % (1823)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 1.03/0.64  % (1832)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 1.03/0.64  % (1821)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 1.03/0.64  % (1813)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 1.03/0.64  % (1816)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 1.03/0.64  % (1816)Refutation not found, incomplete strategy% (1816)------------------------------
% 1.03/0.64  % (1816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.03/0.64  % (1816)Termination reason: Refutation not found, incomplete strategy
% 1.03/0.64  
% 1.03/0.64  % (1816)Memory used [KB]: 9850
% 1.03/0.64  % (1816)Time elapsed: 0.079 s
% 1.03/0.64  % (1816)------------------------------
% 1.03/0.64  % (1816)------------------------------
% 1.03/0.65  % (1837)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 1.03/0.65  % (1825)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 1.03/0.65  % (1815)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 1.03/0.65  % (1818)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 1.03/0.65  % (1822)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 1.03/0.66  % (1822)Refutation not found, incomplete strategy% (1822)------------------------------
% 1.03/0.66  % (1822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.03/0.66  % (1826)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 1.03/0.66  % (1828)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 1.03/0.66  % (1828)Refutation not found, incomplete strategy% (1828)------------------------------
% 1.03/0.66  % (1828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.03/0.66  % (1828)Termination reason: Refutation not found, incomplete strategy
% 1.03/0.66  
% 1.03/0.66  % (1828)Memory used [KB]: 895
% 1.03/0.66  % (1828)Time elapsed: 0.046 s
% 1.03/0.66  % (1828)------------------------------
% 1.03/0.66  % (1828)------------------------------
% 1.03/0.66  % (1822)Termination reason: Refutation not found, incomplete strategy
% 1.03/0.66  
% 1.03/0.66  % (1822)Memory used [KB]: 9850
% 1.03/0.66  % (1822)Time elapsed: 0.086 s
% 1.03/0.66  % (1822)------------------------------
% 1.03/0.66  % (1822)------------------------------
% 1.03/0.66  % (1836)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 1.03/0.67  % SZS status CounterSatisfiable for theBenchmark
% 1.03/0.67  % (1836)# SZS output start Saturation.
% 1.03/0.67  tff(u106,negated_conjecture,
% 1.03/0.67      ~v2_struct_0(sK0)).
% 1.03/0.67  
% 1.03/0.67  tff(u105,negated_conjecture,
% 1.03/0.67      v3_orders_2(sK0)).
% 1.03/0.67  
% 1.03/0.67  tff(u104,negated_conjecture,
% 1.03/0.67      l1_orders_2(sK0)).
% 1.03/0.67  
% 1.03/0.67  tff(u103,axiom,
% 1.03/0.67      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 1.03/0.67  
% 1.03/0.67  tff(u102,negated_conjecture,
% 1.03/0.67      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X1, X0, X2] : ((~m1_subset_1(sK3(X1,k3_waybel_0(sK0,sK1),X2),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(X1,k3_waybel_0(sK0,sK1),X2),X0) | r2_lattice3(X1,k3_waybel_0(sK0,sK1),X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1)))))).
% 1.03/0.67  
% 1.03/0.67  tff(u101,negated_conjecture,
% 1.03/0.67      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X1, X0] : ((~m1_subset_1(sK3(X0,k3_waybel_0(sK0,sK1),X1),u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(X0,k3_waybel_0(sK0,sK1),X1),sK2) | r2_lattice3(X0,k3_waybel_0(sK0,sK1),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))))).
% 1.03/0.67  
% 1.03/0.67  tff(u100,negated_conjecture,
% 1.03/0.67      m1_subset_1(sK2,u1_struct_0(sK0))).
% 1.03/0.67  
% 1.03/0.67  tff(u99,negated_conjecture,
% 1.03/0.67      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.03/0.67  
% 1.03/0.67  tff(u98,axiom,
% 1.03/0.67      (![X1, X0, X2] : ((m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.03/0.67  
% 1.03/0.67  tff(u97,axiom,
% 1.03/0.67      (![X1, X0, X2] : ((~r1_orders_2(X0,sK3(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.03/0.67  
% 1.03/0.67  tff(u96,negated_conjecture,
% 1.03/0.67      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X1, X0] : ((~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X1) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0))))))).
% 1.03/0.67  
% 1.03/0.67  tff(u95,negated_conjecture,
% 1.03/0.67      r1_orders_2(sK0,sK2,sK2)).
% 1.03/0.67  
% 1.03/0.67  tff(u94,negated_conjecture,
% 1.03/0.67      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X0] : ((r1_orders_2(sK0,sK3(sK0,k3_waybel_0(sK0,sK1),X0),sK2) | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))))))).
% 1.03/0.67  
% 1.03/0.67  tff(u93,negated_conjecture,
% 1.03/0.67      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X1, X0] : ((r1_orders_2(sK0,sK3(sK0,k3_waybel_0(sK0,sK1),X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,X0) | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0))))))).
% 1.03/0.67  
% 1.03/0.67  tff(u92,axiom,
% 1.03/0.67      (![X1, X0, X2] : ((r1_orders_2(X0,sK3(X0,X1,X2),sK3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 1.03/0.67  
% 1.03/0.67  tff(u91,negated_conjecture,
% 1.03/0.67      ((~~r2_lattice3(sK0,sK1,sK2)) | ~r2_lattice3(sK0,sK1,sK2))).
% 1.03/0.67  
% 1.03/0.67  tff(u90,axiom,
% 1.03/0.67      (![X1, X3, X0, X2] : ((~r2_lattice3(X0,X3,X1) | r2_lattice3(X0,X3,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 1.03/0.67  
% 1.03/0.67  tff(u89,axiom,
% 1.03/0.67      (![X1, X0, X2, X4] : ((~r2_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.03/0.67  
% 1.03/0.67  tff(u88,negated_conjecture,
% 1.03/0.67      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2))).
% 1.03/0.67  
% 1.03/0.67  tff(u87,negated_conjecture,
% 1.03/0.67      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X0] : ((r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X0) | ~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))))))).
% 1.03/0.67  
% 1.03/0.67  tff(u86,negated_conjecture,
% 1.03/0.67      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X3, X2] : ((~r2_hidden(X3,k3_waybel_0(sK0,sK1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_orders_2(sK0,X3,X2)))))).
% 1.03/0.67  
% 1.03/0.67  tff(u85,negated_conjecture,
% 1.03/0.67      ((~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)) | (![X0] : ((~r2_hidden(X0,k3_waybel_0(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,sK2)))))).
% 1.03/0.67  
% 1.03/0.67  tff(u84,axiom,
% 1.03/0.67      (![X1, X0, X2] : ((r2_hidden(sK3(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.03/0.67  
% 1.03/0.67  tff(u83,negated_conjecture,
% 1.03/0.67      v4_orders_2(sK0)).
% 1.03/0.67  
% 1.03/0.67  tff(u82,axiom,
% 1.03/0.67      (![X1, X3, X0, X2] : ((~r1_lattice3(X0,X3,X2) | r1_lattice3(X0,X3,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 1.03/0.67  
% 1.03/0.67  % (1836)# SZS output end Saturation.
% 1.03/0.67  % (1836)------------------------------
% 1.03/0.67  % (1836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.03/0.67  % (1836)Termination reason: Satisfiable
% 1.03/0.67  
% 1.03/0.67  % (1836)Memory used [KB]: 5373
% 1.03/0.67  % (1836)Time elapsed: 0.095 s
% 1.03/0.67  % (1836)------------------------------
% 1.03/0.67  % (1836)------------------------------
% 1.03/0.67  % (1649)Success in time 0.286 s
%------------------------------------------------------------------------------
