%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:17 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    0
%              Number of atoms          :   40 (  40 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u58,axiom,(
    v1_xboole_0(k1_xboole_0) )).

tff(u57,axiom,(
    ! [X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) )).

tff(u56,axiom,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) )).

tff(u55,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u54,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u53,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X1) ) )).

tff(u52,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u51,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u50,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u49,negated_conjecture,(
    ! [X0] :
      ( r1_lattice3(sK0,X0,sK1)
      | ~ v1_xboole_0(X0) ) )).

tff(u48,axiom,(
    ! [X1,X3,X0,X2] :
      ( r1_lattice3(X0,X3,sK2(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2)
      | ~ v1_xboole_0(X3) ) )).

tff(u47,negated_conjecture,(
    ~ r1_orders_2(sK0,sK1,k4_yellow_0(sK0)) )).

tff(u46,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u45,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u44,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u43,negated_conjecture,(
    v2_yellow_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:04:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (22537)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.48  % (22530)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.48  % (22528)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.49  % (22534)WARNING: option uwaf not known.
% 0.22/0.49  % (22524)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.49  % (22526)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.22/0.49  % (22524)Refutation not found, incomplete strategy% (22524)------------------------------
% 0.22/0.49  % (22524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (22524)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (22524)Memory used [KB]: 5373
% 0.22/0.49  % (22524)Time elapsed: 0.065 s
% 0.22/0.49  % (22524)------------------------------
% 0.22/0.49  % (22524)------------------------------
% 0.22/0.49  % (22539)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.49  % (22539)Refutation not found, incomplete strategy% (22539)------------------------------
% 0.22/0.49  % (22539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (22539)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (22539)Memory used [KB]: 895
% 0.22/0.49  % (22539)Time elapsed: 0.037 s
% 0.22/0.49  % (22539)------------------------------
% 0.22/0.49  % (22539)------------------------------
% 0.22/0.49  % (22540)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.22/0.49  % (22534)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.22/0.49  % (22540)Refutation not found, incomplete strategy% (22540)------------------------------
% 0.22/0.49  % (22540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (22540)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (22540)Memory used [KB]: 5373
% 0.22/0.49  % (22540)Time elapsed: 0.071 s
% 0.22/0.49  % (22540)------------------------------
% 0.22/0.49  % (22540)------------------------------
% 0.22/0.49  % (22529)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.49  % (22529)Refutation not found, incomplete strategy% (22529)------------------------------
% 0.22/0.49  % (22529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (22529)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (22529)Memory used [KB]: 895
% 0.22/0.49  % (22529)Time elapsed: 0.039 s
% 0.22/0.49  % (22529)------------------------------
% 0.22/0.49  % (22529)------------------------------
% 0.22/0.49  % (22536)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.50  % (22533)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.50  % (22533)Refutation not found, incomplete strategy% (22533)------------------------------
% 0.22/0.50  % (22533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22533)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (22533)Memory used [KB]: 9850
% 0.22/0.50  % (22533)Time elapsed: 0.094 s
% 0.22/0.50  % (22533)------------------------------
% 0.22/0.50  % (22533)------------------------------
% 0.22/0.50  % (22543)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.22/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.50  % (22543)# SZS output start Saturation.
% 0.22/0.50  tff(u58,axiom,
% 0.22/0.50      v1_xboole_0(k1_xboole_0)).
% 0.22/0.50  
% 0.22/0.50  tff(u57,axiom,
% 0.22/0.50      (![X0, X2] : ((~r2_hidden(X2,X0) | ~v1_xboole_0(X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u56,axiom,
% 0.22/0.50      (![X0] : ((r2_hidden(sK3(X0),X0) | v1_xboole_0(X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u55,axiom,
% 0.22/0.50      (![X1, X0, X2] : ((r2_hidden(sK2(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u54,negated_conjecture,
% 0.22/0.50      l1_orders_2(sK0)).
% 0.22/0.50  
% 0.22/0.50  tff(u53,axiom,
% 0.22/0.50      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~l1_orders_2(X0) | ~v1_xboole_0(X1))))).
% 0.22/0.50  
% 0.22/0.50  tff(u52,negated_conjecture,
% 0.22/0.50      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.50  
% 0.22/0.50  tff(u51,axiom,
% 0.22/0.50      (![X1, X0, X2] : ((m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u50,axiom,
% 0.22/0.50      (![X1, X0, X2, X4] : ((~r1_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X2,X4) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u49,negated_conjecture,
% 0.22/0.50      (![X0] : ((r1_lattice3(sK0,X0,sK1) | ~v1_xboole_0(X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u48,axiom,
% 0.22/0.50      (![X1, X3, X0, X2] : ((r1_lattice3(X0,X3,sK2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2) | ~v1_xboole_0(X3))))).
% 0.22/0.50  
% 0.22/0.50  tff(u47,negated_conjecture,
% 0.22/0.50      ~r1_orders_2(sK0,sK1,k4_yellow_0(sK0))).
% 0.22/0.50  
% 0.22/0.50  tff(u46,axiom,
% 0.22/0.50      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK2(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u45,negated_conjecture,
% 0.22/0.50      ~v2_struct_0(sK0)).
% 0.22/0.50  
% 0.22/0.50  tff(u44,negated_conjecture,
% 0.22/0.50      v5_orders_2(sK0)).
% 0.22/0.50  
% 0.22/0.50  tff(u43,negated_conjecture,
% 0.22/0.50      v2_yellow_0(sK0)).
% 0.22/0.50  
% 0.22/0.50  % (22543)# SZS output end Saturation.
% 0.22/0.50  % (22543)------------------------------
% 0.22/0.50  % (22543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22543)Termination reason: Satisfiable
% 0.22/0.50  
% 0.22/0.50  % (22543)Memory used [KB]: 5373
% 0.22/0.50  % (22543)Time elapsed: 0.066 s
% 0.22/0.50  % (22543)------------------------------
% 0.22/0.50  % (22543)------------------------------
% 0.22/0.50  % (22523)Success in time 0.137 s
%------------------------------------------------------------------------------
