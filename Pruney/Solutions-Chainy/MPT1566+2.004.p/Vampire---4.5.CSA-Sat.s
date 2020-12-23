%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:17 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   26 (  26 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    0
%              Number of atoms          :   58 (  58 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u41,axiom,
    ( sP4(sK3(sK3(X0))) )).

cnf(u40,axiom,
    ( sP4(k1_xboole_0) )).

cnf(u39,axiom,
    ( ~ sP4(X1)
    | ~ r2_hidden(X0,X1) )).

cnf(u33,axiom,
    ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u28,negated_conjecture,
    ( ~ r1_orders_2(sK0,k3_yellow_0(sK0),sK1) )).

cnf(u59,negated_conjecture,
    ( r2_lattice3(sK0,X0,sK1)
    | r2_hidden(sK2(sK0,X0,sK1),X0) )).

cnf(u60,negated_conjecture,
    ( r2_lattice3(sK0,X0,sK1)
    | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0)) )).

cnf(u51,negated_conjecture,
    ( r2_lattice3(sK0,sK3(sK3(X0)),sK1) )).

cnf(u45,negated_conjecture,
    ( r2_lattice3(sK0,k1_xboole_0,sK1) )).

cnf(u30,axiom,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | r1_orders_2(X0,X4,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u26,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u32,axiom,
    ( ~ l1_orders_2(X0)
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_lattice3(X0,X1,X2) )).

cnf(u31,axiom,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_lattice3(X0,X1,X2) )).

cnf(u48,axiom,
    ( ~ r2_hidden(X0,sK3(sK3(X1))) )).

cnf(u43,axiom,
    ( ~ r2_hidden(X0,k1_xboole_0) )).

cnf(u36,axiom,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2) )).

cnf(u65,negated_conjecture,
    ( ~ r2_hidden(X1,X0)
    | r2_hidden(sK2(sK0,X0,sK1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK0,X1,sK1) )).

cnf(u68,negated_conjecture,
    ( ~ r2_hidden(X1,X0)
    | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK0,X1,sK1) )).

cnf(u35,axiom,
    ( v1_xboole_0(sK3(X0)) )).

cnf(u38,axiom,
    ( ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | sP4(X1) )).

cnf(u34,axiom,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) )).

cnf(u29,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u27,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u46,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(sK2(sK0,X0,X1),X0)
    | r2_lattice3(sK0,X0,X1) )).

cnf(u47,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
    | r2_lattice3(sK0,X0,X1) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(X1)))
    | sP4(X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (29462)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.44  % (29464)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.44  % (29454)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.45  % (29462)Refutation not found, incomplete strategy% (29462)------------------------------
% 0.21/0.45  % (29462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (29462)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (29462)Memory used [KB]: 5373
% 0.21/0.45  % (29462)Time elapsed: 0.069 s
% 0.21/0.45  % (29462)------------------------------
% 0.21/0.45  % (29462)------------------------------
% 0.21/0.45  % (29470)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.21/0.46  % (29456)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.46  % (29465)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.47  % (29465)Refutation not found, incomplete strategy% (29465)------------------------------
% 0.21/0.47  % (29465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (29465)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (29465)Memory used [KB]: 5373
% 0.21/0.47  % (29465)Time elapsed: 0.008 s
% 0.21/0.47  % (29465)------------------------------
% 0.21/0.47  % (29465)------------------------------
% 0.21/0.47  % (29457)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.48  % (29471)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.21/0.48  % (29455)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.48  % (29461)WARNING: option uwaf not known.
% 0.21/0.48  % (29463)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.48  % (29455)Refutation not found, incomplete strategy% (29455)------------------------------
% 0.21/0.48  % (29455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (29455)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (29455)Memory used [KB]: 895
% 0.21/0.48  % (29455)Time elapsed: 0.068 s
% 0.21/0.48  % (29455)------------------------------
% 0.21/0.48  % (29455)------------------------------
% 0.21/0.48  % (29461)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.21/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.48  % (29471)# SZS output start Saturation.
% 0.21/0.48  cnf(u41,axiom,
% 0.21/0.48      sP4(sK3(sK3(X0)))).
% 0.21/0.48  
% 0.21/0.48  cnf(u40,axiom,
% 0.21/0.48      sP4(k1_xboole_0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u39,axiom,
% 0.21/0.48      ~sP4(X1) | ~r2_hidden(X0,X1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u33,axiom,
% 0.21/0.48      ~r1_orders_2(X0,sK2(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u28,negated_conjecture,
% 0.21/0.48      ~r1_orders_2(sK0,k3_yellow_0(sK0),sK1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u59,negated_conjecture,
% 0.21/0.48      r2_lattice3(sK0,X0,sK1) | r2_hidden(sK2(sK0,X0,sK1),X0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u60,negated_conjecture,
% 0.21/0.48      r2_lattice3(sK0,X0,sK1) | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0))).
% 0.21/0.48  
% 0.21/0.48  cnf(u51,negated_conjecture,
% 0.21/0.48      r2_lattice3(sK0,sK3(sK3(X0)),sK1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u45,negated_conjecture,
% 0.21/0.48      r2_lattice3(sK0,k1_xboole_0,sK1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u30,axiom,
% 0.21/0.48      ~r2_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u26,negated_conjecture,
% 0.21/0.48      l1_orders_2(sK0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u32,axiom,
% 0.21/0.48      ~l1_orders_2(X0) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)).
% 0.21/0.48  
% 0.21/0.48  cnf(u31,axiom,
% 0.21/0.48      ~l1_orders_2(X0) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)).
% 0.21/0.48  
% 0.21/0.48  cnf(u48,axiom,
% 0.21/0.48      ~r2_hidden(X0,sK3(sK3(X1)))).
% 0.21/0.48  
% 0.21/0.48  cnf(u43,axiom,
% 0.21/0.48      ~r2_hidden(X0,k1_xboole_0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u36,axiom,
% 0.21/0.48      ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)).
% 0.21/0.48  
% 0.21/0.48  cnf(u65,negated_conjecture,
% 0.21/0.48      ~r2_hidden(X1,X0) | r2_hidden(sK2(sK0,X0,sK1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X1,sK1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u68,negated_conjecture,
% 0.21/0.48      ~r2_hidden(X1,X0) | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X1,sK1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u35,axiom,
% 0.21/0.48      v1_xboole_0(sK3(X0))).
% 0.21/0.48  
% 0.21/0.48  cnf(u38,axiom,
% 0.21/0.48      ~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sP4(X1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u34,axiom,
% 0.21/0.48      m1_subset_1(sK3(X0),k1_zfmisc_1(X0))).
% 0.21/0.48  
% 0.21/0.48  cnf(u29,axiom,
% 0.21/0.48      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.21/0.48  
% 0.21/0.48  cnf(u27,negated_conjecture,
% 0.21/0.48      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.48  
% 0.21/0.48  cnf(u46,negated_conjecture,
% 0.21/0.48      ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK2(sK0,X0,X1),X0) | r2_lattice3(sK0,X0,X1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u47,negated_conjecture,
% 0.21/0.48      ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u42,axiom,
% 0.21/0.48      ~m1_subset_1(X0,k1_zfmisc_1(sK3(X1))) | sP4(X0)).
% 0.21/0.48  
% 0.21/0.48  % (29471)# SZS output end Saturation.
% 0.21/0.48  % (29471)------------------------------
% 0.21/0.48  % (29471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (29471)Termination reason: Satisfiable
% 0.21/0.48  
% 0.21/0.48  % (29471)Memory used [KB]: 5373
% 0.21/0.48  % (29471)Time elapsed: 0.066 s
% 0.21/0.48  % (29471)------------------------------
% 0.21/0.48  % (29471)------------------------------
% 0.21/0.48  % (29447)Success in time 0.134 s
%------------------------------------------------------------------------------
