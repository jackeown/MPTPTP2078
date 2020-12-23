%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:22 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 1.43s
% Verified   : 
% Statistics : Number of clauses        :   23 (  23 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    0
%              Number of atoms          :   57 (  57 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u26,negated_conjecture,
    ( m1_yellow_0(sK1,sK0) )).

cnf(u46,negated_conjecture,
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

cnf(u42,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u35,axiom,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u37,axiom,
    ( r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0) )).

cnf(u52,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,X1) )).

cnf(u38,axiom,
    ( ~ r2_hidden(X1,X0)
    | m1_subset_1(X1,X0)
    | v1_xboole_0(X0) )).

cnf(u51,axiom,
    ( m1_subset_1(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ r1_orders_2(X0,X1,X2)
    | v1_xboole_0(u1_orders_2(X0)) )).

cnf(u48,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) )).

cnf(u47,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) )).

cnf(u28,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) )).

cnf(u27,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u54,negated_conjecture,
    ( ~ m1_subset_1(k4_tarski(X3,X2),u1_orders_2(sK0))
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | r1_orders_2(sK0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | v1_xboole_0(u1_orders_2(sK0)) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u43,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2)
    | ~ r2_hidden(X0,X1) )).

cnf(u39,axiom,
    ( ~ v1_xboole_0(X0)
    | ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X1) )).

cnf(u40,axiom,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | m1_subset_1(X1,X0) )).

cnf(u44,axiom,
    ( ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X0,X1) )).

cnf(u32,negated_conjecture,
    ( sK3 = sK5 )).

cnf(u31,negated_conjecture,
    ( sK2 = sK4 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:10:50 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.51  % (4106)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.51  % (4106)Refutation not found, incomplete strategy% (4106)------------------------------
% 0.22/0.51  % (4106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (4106)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (4106)Memory used [KB]: 10490
% 0.22/0.51  % (4106)Time elapsed: 0.061 s
% 0.22/0.51  % (4106)------------------------------
% 0.22/0.51  % (4106)------------------------------
% 0.22/0.52  % (4114)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.52  % (4114)Refutation not found, incomplete strategy% (4114)------------------------------
% 0.22/0.52  % (4114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (4114)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (4114)Memory used [KB]: 1535
% 0.22/0.52  % (4114)Time elapsed: 0.071 s
% 0.22/0.52  % (4114)------------------------------
% 0.22/0.52  % (4114)------------------------------
% 0.22/0.54  % (4100)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.54  % (4102)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.54  % (4103)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.54  % (4104)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.55  % (4104)Refutation not found, incomplete strategy% (4104)------------------------------
% 0.22/0.55  % (4104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4104)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4104)Memory used [KB]: 10618
% 0.22/0.55  % (4104)Time elapsed: 0.109 s
% 0.22/0.55  % (4104)------------------------------
% 0.22/0.55  % (4104)------------------------------
% 0.22/0.55  % (4115)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.55  % (4107)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.55  % (4116)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.55  % (4118)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.55  % (4119)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.55  % (4118)Refutation not found, incomplete strategy% (4118)------------------------------
% 0.22/0.55  % (4118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4118)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4118)Memory used [KB]: 6140
% 0.22/0.55  % (4118)Time elapsed: 0.112 s
% 0.22/0.55  % (4118)------------------------------
% 0.22/0.55  % (4118)------------------------------
% 0.22/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.56  % (4099)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.56  % (4120)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.43/0.56  % (4110)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.43/0.56  % (4108)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.43/0.56  % (4101)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.43/0.56  % (4121)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.43/0.56  % (4108)Refutation not found, incomplete strategy% (4108)------------------------------
% 1.43/0.56  % (4108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (4108)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (4108)Memory used [KB]: 10490
% 1.43/0.56  % (4108)Time elapsed: 0.123 s
% 1.43/0.56  % (4108)------------------------------
% 1.43/0.56  % (4108)------------------------------
% 1.43/0.56  % (4111)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.43/0.56  % (4121)Refutation not found, incomplete strategy% (4121)------------------------------
% 1.43/0.56  % (4121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (4121)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (4121)Memory used [KB]: 10618
% 1.43/0.56  % (4121)Time elapsed: 0.119 s
% 1.43/0.56  % (4121)------------------------------
% 1.43/0.56  % (4121)------------------------------
% 1.43/0.56  % (4113)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.43/0.56  % (4105)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.43/0.57  % (4105)Refutation not found, incomplete strategy% (4105)------------------------------
% 1.43/0.57  % (4105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (4101)Refutation not found, incomplete strategy% (4101)------------------------------
% 1.43/0.57  % (4101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (4101)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.57  
% 1.43/0.57  % (4101)Memory used [KB]: 10618
% 1.43/0.57  % (4101)Time elapsed: 0.123 s
% 1.43/0.57  % (4101)------------------------------
% 1.43/0.57  % (4101)------------------------------
% 1.43/0.57  % (4105)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.57  
% 1.43/0.57  % (4105)Memory used [KB]: 6012
% 1.43/0.57  % (4105)Time elapsed: 0.124 s
% 1.43/0.57  % (4105)------------------------------
% 1.43/0.57  % (4105)------------------------------
% 1.43/0.57  % (4107)# SZS output start Saturation.
% 1.43/0.57  cnf(u26,negated_conjecture,
% 1.43/0.57      m1_yellow_0(sK1,sK0)).
% 1.43/0.57  
% 1.43/0.57  cnf(u46,negated_conjecture,
% 1.43/0.57      r1_orders_2(sK1,sK2,sK3)).
% 1.43/0.57  
% 1.43/0.57  cnf(u34,negated_conjecture,
% 1.43/0.57      ~r1_orders_2(sK0,sK2,sK3)).
% 1.43/0.57  
% 1.43/0.57  cnf(u25,negated_conjecture,
% 1.43/0.57      l1_orders_2(sK0)).
% 1.43/0.57  
% 1.43/0.57  cnf(u36,axiom,
% 1.43/0.57      ~l1_orders_2(X0) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2)).
% 1.43/0.57  
% 1.43/0.57  cnf(u42,axiom,
% 1.43/0.57      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 1.43/0.57  
% 1.43/0.57  cnf(u35,axiom,
% 1.43/0.57      r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 1.43/0.57  
% 1.43/0.57  cnf(u37,axiom,
% 1.43/0.57      r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)).
% 1.43/0.57  
% 1.43/0.57  cnf(u52,negated_conjecture,
% 1.43/0.57      ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X1)).
% 1.43/0.57  
% 1.43/0.57  cnf(u38,axiom,
% 1.43/0.57      ~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)).
% 1.43/0.57  
% 1.43/0.57  cnf(u51,axiom,
% 1.43/0.57      m1_subset_1(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | v1_xboole_0(u1_orders_2(X0))).
% 1.43/0.57  
% 1.43/0.57  cnf(u48,negated_conjecture,
% 1.43/0.57      m1_subset_1(sK2,u1_struct_0(sK1))).
% 1.43/0.57  
% 1.43/0.57  cnf(u47,negated_conjecture,
% 1.43/0.57      m1_subset_1(sK3,u1_struct_0(sK1))).
% 1.43/0.57  
% 1.43/0.57  cnf(u28,negated_conjecture,
% 1.43/0.57      m1_subset_1(sK3,u1_struct_0(sK0))).
% 1.43/0.57  
% 1.43/0.57  cnf(u27,negated_conjecture,
% 1.43/0.57      m1_subset_1(sK2,u1_struct_0(sK0))).
% 1.43/0.57  
% 1.43/0.57  cnf(u54,negated_conjecture,
% 1.43/0.57      ~m1_subset_1(k4_tarski(X3,X2),u1_orders_2(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_orders_2(sK0,X3,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v1_xboole_0(u1_orders_2(sK0))).
% 1.43/0.57  
% 1.43/0.57  cnf(u41,axiom,
% 1.43/0.57      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 1.43/0.57  
% 1.43/0.57  cnf(u43,axiom,
% 1.43/0.57      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)).
% 1.43/0.57  
% 1.43/0.57  cnf(u39,axiom,
% 1.43/0.57      ~v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X1)).
% 1.43/0.57  
% 1.43/0.57  cnf(u40,axiom,
% 1.43/0.57      ~v1_xboole_0(X0) | ~v1_xboole_0(X1) | m1_subset_1(X1,X0)).
% 1.43/0.57  
% 1.43/0.57  cnf(u44,axiom,
% 1.43/0.57      ~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)).
% 1.43/0.57  
% 1.43/0.57  cnf(u32,negated_conjecture,
% 1.43/0.57      sK3 = sK5).
% 1.43/0.57  
% 1.43/0.57  cnf(u31,negated_conjecture,
% 1.43/0.57      sK2 = sK4).
% 1.43/0.57  
% 1.43/0.57  % (4107)# SZS output end Saturation.
% 1.43/0.57  % (4107)------------------------------
% 1.43/0.57  % (4107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (4107)Termination reason: Satisfiable
% 1.43/0.57  
% 1.43/0.57  % (4107)Memory used [KB]: 1663
% 1.43/0.57  % (4107)Time elapsed: 0.071 s
% 1.43/0.57  % (4107)------------------------------
% 1.43/0.57  % (4107)------------------------------
% 1.43/0.57  % (4097)Success in time 0.196 s
%------------------------------------------------------------------------------
