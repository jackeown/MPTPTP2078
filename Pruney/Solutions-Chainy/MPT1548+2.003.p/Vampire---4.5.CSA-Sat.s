%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:02 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   22 (  22 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    0
%              Number of atoms          :   62 (  62 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u22,axiom,
    ( ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_lattice3(X0,X1,X2) )).

cnf(u78,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK1,X0,X1) )).

cnf(u20,axiom,
    ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_orders_2(X0,X1,X2) )).

% (31143)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
cnf(u21,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) )).

cnf(u25,axiom,
    ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,X2) )).

cnf(u59,negated_conjecture,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

cnf(u19,axiom,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) )).

cnf(u26,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
    | X0 = X2 )).

cnf(u27,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
    | X1 = X3 )).

cnf(u43,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r2_hidden(sK3(sK1,X1,X0),X1)
    | r2_lattice3(sK1,X1,X0) )).

cnf(u63,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK1,X1,X0),u1_struct_0(sK0))
    | r2_lattice3(sK1,X1,X0) )).

cnf(u24,axiom,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_hidden(sK3(X0,X1,X2),X1)
    | r2_lattice3(X0,X1,X2) )).

cnf(u23,axiom,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | r2_lattice3(X0,X1,X2) )).

cnf(u18,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u15,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u28,axiom,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = X1
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) )).

cnf(u50,axiom,
    ( ~ l1_orders_2(X0)
    | u1_orders_2(X0) = X2
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) )).

% (31142)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
cnf(u56,negated_conjecture,
    ( u1_orders_2(sK0) = u1_orders_2(sK1) )).

cnf(u36,negated_conjecture,
    ( u1_struct_0(sK0) = u1_struct_0(sK1) )).

cnf(u30,negated_conjecture,
    ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK0) = X2 )).

cnf(u57,negated_conjecture,
    ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_orders_2(sK0) = X1 )).

cnf(u17,negated_conjecture,
    ( k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2) )).

% (31129)Refutation not found, incomplete strategy% (31129)------------------------------
% (31129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31129)Termination reason: Refutation not found, incomplete strategy

% (31129)Memory used [KB]: 10746
% (31129)Time elapsed: 0.135 s
% (31129)------------------------------
% (31129)------------------------------
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 21:01:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (31149)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (31141)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (31134)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (31131)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (31149)Refutation not found, incomplete strategy% (31149)------------------------------
% 0.20/0.53  % (31149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (31134)Refutation not found, incomplete strategy% (31134)------------------------------
% 0.20/0.53  % (31134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (31149)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (31149)Memory used [KB]: 10746
% 0.20/0.53  % (31149)Time elapsed: 0.062 s
% 0.20/0.53  % (31149)------------------------------
% 0.20/0.53  % (31149)------------------------------
% 0.20/0.53  % (31134)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (31134)Memory used [KB]: 6268
% 0.20/0.53  % (31134)Time elapsed: 0.077 s
% 0.20/0.53  % (31134)------------------------------
% 0.20/0.53  % (31134)------------------------------
% 0.20/0.53  % (31130)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (31130)Refutation not found, incomplete strategy% (31130)------------------------------
% 0.20/0.53  % (31130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (31130)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (31130)Memory used [KB]: 10746
% 0.20/0.53  % (31130)Time elapsed: 0.127 s
% 0.20/0.53  % (31130)------------------------------
% 0.20/0.53  % (31130)------------------------------
% 0.20/0.53  % (31129)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (31131)Refutation not found, incomplete strategy% (31131)------------------------------
% 0.20/0.54  % (31131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (31131)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (31131)Memory used [KB]: 6140
% 0.20/0.54  % (31131)Time elapsed: 0.127 s
% 0.20/0.54  % (31131)------------------------------
% 0.20/0.54  % (31131)------------------------------
% 0.20/0.54  % (31128)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (31151)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (31133)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (31154)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.54  % (31146)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (31144)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (31156)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (31137)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (31140)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (31133)# SZS output start Saturation.
% 0.20/0.55  cnf(u22,axiom,
% 0.20/0.55      ~r2_hidden(X3,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X3,X2) | ~r2_lattice3(X0,X1,X2)).
% 0.20/0.55  
% 0.20/0.55  cnf(u78,negated_conjecture,
% 0.20/0.55      ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK1,X0,X1)).
% 0.20/0.55  
% 0.20/0.55  cnf(u20,axiom,
% 0.20/0.55      ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2)).
% 0.20/0.55  
% 0.20/0.55  % (31143)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  cnf(u21,axiom,
% 0.20/0.55      ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~l1_orders_2(X0)).
% 0.20/0.55  
% 0.20/0.55  cnf(u25,axiom,
% 0.20/0.55      ~r1_orders_2(X0,sK3(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)).
% 0.20/0.55  
% 0.20/0.55  cnf(u59,negated_conjecture,
% 0.20/0.55      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.20/0.55  
% 0.20/0.55  cnf(u19,axiom,
% 0.20/0.55      m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)).
% 0.20/0.55  
% 0.20/0.55  cnf(u26,axiom,
% 0.20/0.55      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2).
% 0.20/0.55  
% 0.20/0.55  cnf(u27,axiom,
% 0.20/0.55      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3).
% 0.20/0.55  
% 0.20/0.55  cnf(u43,negated_conjecture,
% 0.20/0.55      ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(sK3(sK1,X1,X0),X1) | r2_lattice3(sK1,X1,X0)).
% 0.20/0.55  
% 0.20/0.55  cnf(u63,negated_conjecture,
% 0.20/0.55      ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK3(sK1,X1,X0),u1_struct_0(sK0)) | r2_lattice3(sK1,X1,X0)).
% 0.20/0.55  
% 0.20/0.55  cnf(u24,axiom,
% 0.20/0.55      ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(sK3(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2)).
% 0.20/0.55  
% 0.20/0.55  cnf(u23,axiom,
% 0.20/0.55      ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)).
% 0.20/0.55  
% 0.20/0.55  cnf(u18,negated_conjecture,
% 0.20/0.55      l1_orders_2(sK0)).
% 0.20/0.55  
% 0.20/0.55  cnf(u15,negated_conjecture,
% 0.20/0.55      l1_orders_2(sK1)).
% 0.20/0.55  
% 0.20/0.55  cnf(u28,axiom,
% 0.20/0.55      ~l1_orders_2(X0) | u1_struct_0(X0) = X1 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.20/0.55  
% 0.20/0.55  cnf(u50,axiom,
% 0.20/0.55      ~l1_orders_2(X0) | u1_orders_2(X0) = X2 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.20/0.55  
% 0.20/0.55  % (31142)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  cnf(u56,negated_conjecture,
% 0.20/0.55      u1_orders_2(sK0) = u1_orders_2(sK1)).
% 0.20/0.55  
% 0.20/0.55  cnf(u36,negated_conjecture,
% 0.20/0.55      u1_struct_0(sK0) = u1_struct_0(sK1)).
% 0.20/0.55  
% 0.20/0.55  cnf(u30,negated_conjecture,
% 0.20/0.55      g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_struct_0(sK0) = X2).
% 0.20/0.55  
% 0.20/0.55  cnf(u57,negated_conjecture,
% 0.20/0.55      g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_orders_2(sK0) = X1).
% 0.20/0.55  
% 0.20/0.55  cnf(u17,negated_conjecture,
% 0.20/0.55      k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2)).
% 0.20/0.55  
% 0.20/0.55  % (31129)Refutation not found, incomplete strategy% (31129)------------------------------
% 0.20/0.55  % (31129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (31129)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (31129)Memory used [KB]: 10746
% 0.20/0.55  % (31129)Time elapsed: 0.135 s
% 0.20/0.55  % (31129)------------------------------
% 0.20/0.55  % (31129)------------------------------
% 0.20/0.55  % (31133)# SZS output end Saturation.
% 0.20/0.55  % (31133)------------------------------
% 0.20/0.55  % (31133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (31133)Termination reason: Satisfiable
% 0.20/0.55  
% 0.20/0.55  % (31133)Memory used [KB]: 6268
% 0.20/0.55  % (31133)Time elapsed: 0.128 s
% 0.20/0.55  % (31133)------------------------------
% 0.20/0.55  % (31133)------------------------------
% 0.20/0.55  % (31126)Success in time 0.184 s
%------------------------------------------------------------------------------
