%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:03 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
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
    | r1_orders_2(X0,X2,X3)
    | ~ r1_lattice3(X0,X1,X2) )).

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

cnf(u21,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) )).

cnf(u25,axiom,
    ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,X2) )).

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
    | r1_lattice3(sK1,X1,X0) )).

cnf(u63,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK1,X1,X0),u1_struct_0(sK0))
    | r1_lattice3(sK1,X1,X0) )).

cnf(u24,axiom,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_hidden(sK3(X0,X1,X2),X1)
    | r1_lattice3(X0,X1,X2) )).

cnf(u23,axiom,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | r1_lattice3(X0,X1,X2) )).

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
    ( k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:53:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (21140)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (21159)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (21140)Refutation not found, incomplete strategy% (21140)------------------------------
% 0.21/0.51  % (21140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21140)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21140)Memory used [KB]: 10746
% 0.21/0.51  % (21140)Time elapsed: 0.078 s
% 0.21/0.51  % (21140)------------------------------
% 0.21/0.51  % (21140)------------------------------
% 0.21/0.51  % (21153)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (21153)Refutation not found, incomplete strategy% (21153)------------------------------
% 0.21/0.51  % (21153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21153)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21153)Memory used [KB]: 10746
% 0.21/0.51  % (21153)Time elapsed: 0.050 s
% 0.21/0.51  % (21153)------------------------------
% 0.21/0.51  % (21153)------------------------------
% 0.21/0.52  % (21145)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (21136)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.53  % (21136)# SZS output start Saturation.
% 0.21/0.53  cnf(u22,axiom,
% 0.21/0.53      ~r2_hidden(X3,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X2,X3) | ~r1_lattice3(X0,X1,X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u78,negated_conjecture,
% 0.21/0.53      ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK1,X0,X1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u20,axiom,
% 0.21/0.53      ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u21,axiom,
% 0.21/0.53      ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~l1_orders_2(X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u25,axiom,
% 0.21/0.53      ~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u59,negated_conjecture,
% 0.21/0.53      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.21/0.53  
% 0.21/0.53  cnf(u19,axiom,
% 0.21/0.53      m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u26,axiom,
% 0.21/0.53      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2).
% 0.21/0.53  
% 0.21/0.53  cnf(u27,axiom,
% 0.21/0.53      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3).
% 0.21/0.53  
% 0.21/0.53  cnf(u43,negated_conjecture,
% 0.21/0.53      ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(sK3(sK1,X1,X0),X1) | r1_lattice3(sK1,X1,X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u63,negated_conjecture,
% 0.21/0.53      ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK3(sK1,X1,X0),u1_struct_0(sK0)) | r1_lattice3(sK1,X1,X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u24,axiom,
% 0.21/0.53      ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(sK3(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u23,axiom,
% 0.21/0.53      ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u18,negated_conjecture,
% 0.21/0.53      l1_orders_2(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u15,negated_conjecture,
% 0.21/0.53      l1_orders_2(sK1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u28,axiom,
% 0.21/0.53      ~l1_orders_2(X0) | u1_struct_0(X0) = X1 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u50,axiom,
% 0.21/0.53      ~l1_orders_2(X0) | u1_orders_2(X0) = X2 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u56,negated_conjecture,
% 0.21/0.53      u1_orders_2(sK0) = u1_orders_2(sK1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u36,negated_conjecture,
% 0.21/0.53      u1_struct_0(sK0) = u1_struct_0(sK1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u30,negated_conjecture,
% 0.21/0.53      g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_struct_0(sK0) = X2).
% 0.21/0.53  
% 0.21/0.53  cnf(u57,negated_conjecture,
% 0.21/0.53      g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_orders_2(sK0) = X1).
% 0.21/0.53  
% 0.21/0.53  cnf(u17,negated_conjecture,
% 0.21/0.53      k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2)).
% 0.21/0.53  
% 0.21/0.53  % (21136)# SZS output end Saturation.
% 0.21/0.53  % (21136)------------------------------
% 0.21/0.53  % (21136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21136)Termination reason: Satisfiable
% 0.21/0.53  
% 0.21/0.53  % (21136)Memory used [KB]: 6268
% 0.21/0.53  % (21136)Time elapsed: 0.075 s
% 0.21/0.53  % (21136)------------------------------
% 0.21/0.53  % (21136)------------------------------
% 0.21/0.53  % (21126)Success in time 0.168 s
%------------------------------------------------------------------------------
