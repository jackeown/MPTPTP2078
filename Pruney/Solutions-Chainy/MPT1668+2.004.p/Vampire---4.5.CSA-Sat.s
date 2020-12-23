%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:15 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of clauses        :   27 (  27 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    0
%              Number of atoms          :   74 (  74 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u23,negated_conjecture,
    ( v14_waybel_0(sK1,sK0)
    | sK1 = k5_waybel_0(sK0,sK2) )).

cnf(u28,axiom,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | r1_orders_2(X0,X3,X2)
    | ~ l1_orders_2(X0) )).

cnf(u58,negated_conjecture,
    ( r1_orders_2(sK0,sK3(sK0,X1,X0),sK3(sK0,X1,X0))
    | r2_lattice3(sK0,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u52,negated_conjecture,
    ( r1_orders_2(sK0,X0,X0)
    | ~ r2_hidden(X0,sK1) )).

cnf(u51,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK2)
    | v14_waybel_0(sK1,sK0) )).

cnf(u31,axiom,
    ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,X2) )).

cnf(u27,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u32,axiom,
    ( ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,X1) )).

cnf(u30,axiom,
    ( ~ l1_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X1)
    | r2_lattice3(X0,X1,X2) )).

cnf(u26,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u25,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u29,axiom,
    ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,X2) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | v14_waybel_0(sK1,sK0) )).

cnf(u24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u46,negated_conjecture,
    ( m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r2_hidden(X0,sK1) )).

cnf(u50,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,X0) )).

cnf(u39,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2) )).

cnf(u54,negated_conjecture,
    ( r2_hidden(sK3(sK0,X1,X0),X2)
    | r2_lattice3(sK0,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X1,X2) )).

cnf(u53,negated_conjecture,
    ( r2_hidden(sK3(sK0,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r2_lattice3(sK0,X1,X0) )).

cnf(u37,axiom,
    ( r2_hidden(sK4(X0,X1),X0)
    | r1_tarski(X0,X1) )).

cnf(u36,axiom,
    ( ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1)
    | ~ r1_tarski(X0,X1) )).

cnf(u38,axiom,
    ( ~ r2_hidden(sK4(X0,X1),X1)
    | r1_tarski(X0,X1) )).

cnf(u40,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u35,axiom,
    ( ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 )).

cnf(u45,axiom,
    ( ~ r1_tarski(X0,X2)
    | r2_hidden(sK4(X0,X1),X2)
    | r1_tarski(X0,X1) )).

cnf(u55,negated_conjecture,
    ( ~ r1_tarski(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r1_tarski(X0,X2)
    | r2_hidden(sK3(sK0,X0,X1),X3)
    | r2_lattice3(sK0,X0,X1) )).

cnf(u21,negated_conjecture,
    ( sK1 != k5_waybel_0(sK0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ v14_waybel_0(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:49:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.45  % (27989)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.45  % (27981)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.46  % (27989)Refutation not found, incomplete strategy% (27989)------------------------------
% 0.19/0.46  % (27989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (27989)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (27989)Memory used [KB]: 10746
% 0.19/0.46  % (27989)Time elapsed: 0.055 s
% 0.19/0.46  % (27989)------------------------------
% 0.19/0.46  % (27989)------------------------------
% 0.19/0.47  % (27973)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.19/0.47  % (27973)# SZS output start Saturation.
% 0.19/0.47  cnf(u23,negated_conjecture,
% 0.19/0.47      v14_waybel_0(sK1,sK0) | sK1 = k5_waybel_0(sK0,sK2)).
% 0.19/0.47  
% 0.19/0.47  cnf(u28,axiom,
% 0.19/0.47      ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X3,X2) | ~l1_orders_2(X0)).
% 0.19/0.47  
% 0.19/0.47  cnf(u58,negated_conjecture,
% 0.19/0.47      r1_orders_2(sK0,sK3(sK0,X1,X0),sK3(sK0,X1,X0)) | r2_lattice3(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 0.19/0.47  
% 0.19/0.47  cnf(u52,negated_conjecture,
% 0.19/0.47      r1_orders_2(sK0,X0,X0) | ~r2_hidden(X0,sK1)).
% 0.19/0.47  
% 0.19/0.47  cnf(u51,negated_conjecture,
% 0.19/0.47      r1_orders_2(sK0,sK2,sK2) | v14_waybel_0(sK1,sK0)).
% 0.19/0.47  
% 0.19/0.47  cnf(u31,axiom,
% 0.19/0.47      ~r1_orders_2(X0,sK3(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)).
% 0.19/0.47  
% 0.19/0.47  cnf(u27,negated_conjecture,
% 0.19/0.47      l1_orders_2(sK0)).
% 0.19/0.47  
% 0.19/0.47  cnf(u32,axiom,
% 0.19/0.47      ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1)).
% 0.19/0.47  
% 0.19/0.47  cnf(u30,axiom,
% 0.19/0.47      ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK3(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2)).
% 0.19/0.47  
% 0.19/0.47  cnf(u26,negated_conjecture,
% 0.19/0.47      v3_orders_2(sK0)).
% 0.19/0.47  
% 0.19/0.47  cnf(u25,negated_conjecture,
% 0.19/0.47      ~v2_struct_0(sK0)).
% 0.19/0.47  
% 0.19/0.47  cnf(u29,axiom,
% 0.19/0.47      m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)).
% 0.19/0.47  
% 0.19/0.47  cnf(u22,negated_conjecture,
% 0.19/0.47      m1_subset_1(sK2,u1_struct_0(sK0)) | v14_waybel_0(sK1,sK0)).
% 0.19/0.47  
% 0.19/0.47  cnf(u24,negated_conjecture,
% 0.19/0.47      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.19/0.47  
% 0.19/0.48  cnf(u46,negated_conjecture,
% 0.19/0.48      m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1)).
% 0.19/0.48  
% 0.19/0.48  cnf(u50,negated_conjecture,
% 0.19/0.48      ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X0)).
% 0.19/0.48  
% 0.19/0.48  cnf(u39,axiom,
% 0.19/0.48      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)).
% 0.19/0.48  
% 0.19/0.48  cnf(u54,negated_conjecture,
% 0.19/0.48      r2_hidden(sK3(sK0,X1,X0),X2) | r2_lattice3(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_tarski(X1,X2)).
% 0.19/0.48  
% 0.19/0.48  cnf(u53,negated_conjecture,
% 0.19/0.48      r2_hidden(sK3(sK0,X1,X0),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,X1,X0)).
% 0.19/0.48  
% 0.19/0.48  cnf(u37,axiom,
% 0.19/0.48      r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)).
% 0.19/0.48  
% 0.19/0.48  cnf(u36,axiom,
% 0.19/0.48      ~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)).
% 0.19/0.48  
% 0.19/0.48  cnf(u38,axiom,
% 0.19/0.48      ~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)).
% 0.19/0.48  
% 0.19/0.48  cnf(u40,axiom,
% 0.19/0.48      r1_tarski(X1,X1)).
% 0.19/0.48  
% 0.19/0.48  cnf(u35,axiom,
% 0.19/0.48      ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1).
% 0.19/0.48  
% 0.19/0.48  cnf(u45,axiom,
% 0.19/0.48      ~r1_tarski(X0,X2) | r2_hidden(sK4(X0,X1),X2) | r1_tarski(X0,X1)).
% 0.19/0.48  
% 0.19/0.48  cnf(u55,negated_conjecture,
% 0.19/0.48      ~r1_tarski(X2,X3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_tarski(X0,X2) | r2_hidden(sK3(sK0,X0,X1),X3) | r2_lattice3(sK0,X0,X1)).
% 0.19/0.48  
% 0.19/0.48  cnf(u21,negated_conjecture,
% 0.19/0.48      sK1 != k5_waybel_0(sK0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v14_waybel_0(sK1,sK0)).
% 0.19/0.48  
% 0.19/0.48  % (27973)# SZS output end Saturation.
% 0.19/0.48  % (27973)------------------------------
% 0.19/0.48  % (27973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (27973)Termination reason: Satisfiable
% 0.19/0.48  
% 0.19/0.48  % (27973)Memory used [KB]: 6268
% 0.19/0.48  % (27973)Time elapsed: 0.066 s
% 0.19/0.48  % (27973)------------------------------
% 0.19/0.48  % (27973)------------------------------
% 0.19/0.48  % (27965)Success in time 0.13 s
%------------------------------------------------------------------------------
