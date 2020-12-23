%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:52 EST 2020

% Result     : CounterSatisfiable 1.35s
% Output     : Saturation 1.35s
% Verified   : 
% Statistics : Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    0
%              Number of atoms          :   41 (  41 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u13,negated_conjecture,
    ( v1_waybel_0(sK2,sK0) )).

cnf(u24,negated_conjecture,
    ( ~ v1_waybel_0(sK2,sK1) )).

cnf(u63,negated_conjecture,
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

cnf(u56,negated_conjecture,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

cnf(u19,axiom,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) )).

cnf(u15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u22,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
    | X0 = X2 )).

cnf(u23,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
    | X1 = X3 )).

cnf(u18,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u16,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u26,axiom,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = X1
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) )).

cnf(u47,axiom,
    ( ~ l1_orders_2(X0)
    | u1_orders_2(X0) = X2
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) )).

cnf(u53,negated_conjecture,
    ( u1_orders_2(sK0) = u1_orders_2(sK1) )).

cnf(u34,negated_conjecture,
    ( u1_struct_0(sK1) = u1_struct_0(sK0) )).

cnf(u12,negated_conjecture,
    ( sK2 = sK3 )).

cnf(u28,negated_conjecture,
    ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK0) = X2 )).

cnf(u54,negated_conjecture,
    ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_orders_2(sK0) = X1 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:44:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.54  % (15812)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (15794)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.54  % (15796)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.35/0.55  % SZS status CounterSatisfiable for theBenchmark
% 1.35/0.55  % (15796)# SZS output start Saturation.
% 1.35/0.55  cnf(u13,negated_conjecture,
% 1.35/0.55      v1_waybel_0(sK2,sK0)).
% 1.35/0.55  
% 1.35/0.55  cnf(u24,negated_conjecture,
% 1.35/0.55      ~v1_waybel_0(sK2,sK1)).
% 1.35/0.55  
% 1.35/0.55  cnf(u63,negated_conjecture,
% 1.35/0.55      ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK1,X0,X1)).
% 1.35/0.55  
% 1.35/0.55  cnf(u20,axiom,
% 1.35/0.55      ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2)).
% 1.35/0.55  
% 1.35/0.55  cnf(u21,axiom,
% 1.35/0.55      ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~l1_orders_2(X0)).
% 1.35/0.55  
% 1.35/0.55  cnf(u56,negated_conjecture,
% 1.35/0.55      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 1.35/0.55  
% 1.35/0.55  cnf(u19,axiom,
% 1.35/0.55      m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)).
% 1.35/0.55  
% 1.35/0.55  cnf(u15,negated_conjecture,
% 1.35/0.55      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.35/0.55  
% 1.35/0.55  cnf(u22,axiom,
% 1.35/0.55      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2).
% 1.35/0.55  
% 1.35/0.55  cnf(u23,axiom,
% 1.35/0.55      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3).
% 1.35/0.55  
% 1.35/0.55  cnf(u18,negated_conjecture,
% 1.35/0.55      l1_orders_2(sK0)).
% 1.35/0.55  
% 1.35/0.55  cnf(u16,negated_conjecture,
% 1.35/0.55      l1_orders_2(sK1)).
% 1.35/0.55  
% 1.35/0.55  cnf(u26,axiom,
% 1.35/0.55      ~l1_orders_2(X0) | u1_struct_0(X0) = X1 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 1.35/0.55  
% 1.35/0.55  cnf(u47,axiom,
% 1.35/0.55      ~l1_orders_2(X0) | u1_orders_2(X0) = X2 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 1.35/0.55  
% 1.35/0.55  cnf(u53,negated_conjecture,
% 1.35/0.55      u1_orders_2(sK0) = u1_orders_2(sK1)).
% 1.35/0.55  
% 1.35/0.55  cnf(u34,negated_conjecture,
% 1.35/0.55      u1_struct_0(sK1) = u1_struct_0(sK0)).
% 1.35/0.55  
% 1.35/0.55  cnf(u12,negated_conjecture,
% 1.35/0.55      sK2 = sK3).
% 1.35/0.55  
% 1.35/0.55  cnf(u28,negated_conjecture,
% 1.35/0.55      g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_struct_0(sK0) = X2).
% 1.35/0.55  
% 1.35/0.55  cnf(u54,negated_conjecture,
% 1.35/0.55      g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_orders_2(sK0) = X1).
% 1.35/0.55  
% 1.35/0.55  % (15796)# SZS output end Saturation.
% 1.35/0.55  % (15796)------------------------------
% 1.35/0.55  % (15796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (15796)Termination reason: Satisfiable
% 1.35/0.55  
% 1.35/0.55  % (15796)Memory used [KB]: 6268
% 1.35/0.55  % (15796)Time elapsed: 0.123 s
% 1.35/0.55  % (15796)------------------------------
% 1.35/0.55  % (15796)------------------------------
% 1.35/0.55  % (15789)Success in time 0.19 s
%------------------------------------------------------------------------------
