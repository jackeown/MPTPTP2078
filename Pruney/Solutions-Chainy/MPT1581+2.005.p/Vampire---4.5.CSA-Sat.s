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
% DateTime   : Thu Dec  3 13:16:22 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    0
%              Number of atoms          :   42 (  42 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u26,negated_conjecture,
    ( m1_yellow_0(sK1,sK0) )).

cnf(u43,negated_conjecture,
    ( r1_orders_2(sK1,sK2,sK3) )).

cnf(u34,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,sK3) )).

cnf(u25,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u36,axiom,
    ( ~ l1_orders_2(X0)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,X2) )).

cnf(u39,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u35,axiom,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u37,axiom,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X0,X1) )).

cnf(u46,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,X1) )).

cnf(u41,axiom,
    ( ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X0,X1) )).

cnf(u45,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) )).

cnf(u44,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) )).

% (24009)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
cnf(u28,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) )).

cnf(u27,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u48,negated_conjecture,
    ( ~ m1_subset_1(k4_tarski(X3,X2),u1_orders_2(sK0))
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | r1_orders_2(sK0,X3,X2)
    | v1_xboole_0(u1_orders_2(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0)) )).

cnf(u38,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u40,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2)
    | ~ r2_hidden(X0,X1) )).

cnf(u32,negated_conjecture,
    ( sK3 = sK5 )).

cnf(u31,negated_conjecture,
    ( sK2 = sK4 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:28:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (24014)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.52  % (24002)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.52  % (23998)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.52  % (24002)Refutation not found, incomplete strategy% (24002)------------------------------
% 0.21/0.52  % (24002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24002)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24002)Memory used [KB]: 10618
% 0.21/0.52  % (24002)Time elapsed: 0.093 s
% 0.21/0.52  % (24002)------------------------------
% 0.21/0.52  % (24002)------------------------------
% 0.21/0.52  % (24000)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.52  % (23999)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.52  % (23999)Refutation not found, incomplete strategy% (23999)------------------------------
% 0.21/0.52  % (23999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23999)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23999)Memory used [KB]: 10618
% 0.21/0.52  % (23999)Time elapsed: 0.097 s
% 0.21/0.52  % (23999)------------------------------
% 0.21/0.52  % (23999)------------------------------
% 0.21/0.52  % (24019)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.53  % (24019)Refutation not found, incomplete strategy% (24019)------------------------------
% 0.21/0.53  % (24019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24019)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (24019)Memory used [KB]: 10618
% 0.21/0.53  % (24019)Time elapsed: 0.051 s
% 0.21/0.53  % (24019)------------------------------
% 0.21/0.53  % (24019)------------------------------
% 0.21/0.53  % (24001)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.53  % (23996)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.54  % (24003)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (24003)Refutation not found, incomplete strategy% (24003)------------------------------
% 0.21/0.54  % (24003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24003)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24003)Memory used [KB]: 6012
% 0.21/0.54  % (24003)Time elapsed: 0.064 s
% 0.21/0.54  % (24003)------------------------------
% 0.21/0.54  % (24003)------------------------------
% 0.21/0.54  % (24013)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.54  % (24012)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.54  % (24012)Refutation not found, incomplete strategy% (24012)------------------------------
% 0.21/0.54  % (24012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24012)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24012)Memory used [KB]: 1535
% 0.21/0.54  % (24012)Time elapsed: 0.115 s
% 0.21/0.54  % (24012)------------------------------
% 0.21/0.54  % (24012)------------------------------
% 0.21/0.54  % (24017)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.54  % (24016)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.54  % (24011)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.54  % (24016)Refutation not found, incomplete strategy% (24016)------------------------------
% 0.21/0.54  % (24016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24016)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24016)Memory used [KB]: 6140
% 0.21/0.54  % (24016)Time elapsed: 0.114 s
% 0.21/0.54  % (24016)------------------------------
% 0.21/0.54  % (24016)------------------------------
% 0.21/0.54  % (24007)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.55  % (24005)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.55  % (24005)# SZS output start Saturation.
% 0.21/0.55  cnf(u26,negated_conjecture,
% 0.21/0.55      m1_yellow_0(sK1,sK0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u43,negated_conjecture,
% 0.21/0.55      r1_orders_2(sK1,sK2,sK3)).
% 0.21/0.55  
% 0.21/0.55  cnf(u34,negated_conjecture,
% 0.21/0.55      ~r1_orders_2(sK0,sK2,sK3)).
% 0.21/0.55  
% 0.21/0.55  cnf(u25,negated_conjecture,
% 0.21/0.55      l1_orders_2(sK0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u36,axiom,
% 0.21/0.55      ~l1_orders_2(X0) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u39,axiom,
% 0.21/0.55      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u35,axiom,
% 0.21/0.55      r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u37,axiom,
% 0.21/0.55      r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u46,negated_conjecture,
% 0.21/0.55      ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u41,axiom,
% 0.21/0.55      ~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u45,negated_conjecture,
% 0.21/0.55      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u44,negated_conjecture,
% 0.21/0.55      m1_subset_1(sK3,u1_struct_0(sK1))).
% 0.21/0.55  
% 0.21/0.55  % (24009)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.55  cnf(u28,negated_conjecture,
% 0.21/0.55      m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u27,negated_conjecture,
% 0.21/0.55      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u48,negated_conjecture,
% 0.21/0.55      ~m1_subset_1(k4_tarski(X3,X2),u1_orders_2(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_orders_2(sK0,X3,X2) | v1_xboole_0(u1_orders_2(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u38,axiom,
% 0.21/0.55      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u40,axiom,
% 0.21/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u32,negated_conjecture,
% 0.21/0.55      sK3 = sK5).
% 0.21/0.55  
% 0.21/0.55  cnf(u31,negated_conjecture,
% 0.21/0.55      sK2 = sK4).
% 0.21/0.55  
% 0.21/0.55  % (24005)# SZS output end Saturation.
% 0.21/0.55  % (24005)------------------------------
% 0.21/0.55  % (24005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24005)Termination reason: Satisfiable
% 0.21/0.55  
% 0.21/0.55  % (24005)Memory used [KB]: 1663
% 0.21/0.55  % (24005)Time elapsed: 0.114 s
% 0.21/0.55  % (24005)------------------------------
% 0.21/0.55  % (24005)------------------------------
% 0.21/0.55  % (23995)Success in time 0.186 s
%------------------------------------------------------------------------------
