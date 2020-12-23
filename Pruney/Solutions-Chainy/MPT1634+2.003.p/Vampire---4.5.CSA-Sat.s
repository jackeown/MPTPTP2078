%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:56 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    0
%              Number of atoms          :   45 (  45 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal clause size      :    4 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u27,negated_conjecture,
    ( r2_hidden(sK2(sK1,X0),X0)
    | m1_subset_1(sK2(sK1,X0),u1_struct_0(sK0))
    | sK1 = X0 )).

cnf(u30,negated_conjecture,
    ( m1_subset_1(sK2(sK1,X0),u1_struct_0(sK0))
    | sK1 = X0
    | ~ r2_hidden(sK2(sK1,X0),sK1) )).

% (4720)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
cnf(u22,negated_conjecture,
    ( r2_hidden(sK2(X0,sK1),X0)
    | m1_subset_1(sK2(X0,sK1),u1_struct_0(sK0))
    | sK1 = X0 )).

cnf(u11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u16,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | X0 = X1
    | r2_hidden(sK2(X0,X1),X0)
    | m1_subset_1(sK2(X0,X1),X2) )).

cnf(u24,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | sK1 = X0
    | m1_subset_1(sK2(X0,sK1),u1_struct_0(sK0))
    | m1_subset_1(sK2(X0,sK1),X1) )).

cnf(u17,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | X0 = X1
    | r2_hidden(sK2(X0,X1),X1)
    | m1_subset_1(sK2(X0,X1),X2) )).

cnf(u29,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | sK1 = X1
    | m1_subset_1(sK2(sK1,X1),u1_struct_0(sK0))
    | m1_subset_1(sK2(sK1,X1),X2) )).

cnf(u27_001,negated_conjecture,
    ( r2_hidden(sK2(sK1,X0),X0)
    | m1_subset_1(sK2(sK1,X0),u1_struct_0(sK0))
    | sK1 = X0 )).

cnf(u22_002,negated_conjecture,
    ( r2_hidden(sK2(X0,sK1),X0)
    | m1_subset_1(sK2(X0,sK1),u1_struct_0(sK0))
    | sK1 = X0 )).

cnf(u13,axiom,
    ( r2_hidden(sK2(X0,X1),X1)
    | r2_hidden(sK2(X0,X1),X0)
    | X0 = X1 )).

cnf(u13_003,axiom,
    ( r2_hidden(sK2(X0,X1),X1)
    | r2_hidden(sK2(X0,X1),X0)
    | X0 = X1 )).

cnf(u14,axiom,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | ~ r2_hidden(sK2(X0,X1),X0)
    | X0 = X1 )).

cnf(u15,axiom,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2) )).

cnf(u12,negated_conjecture,
    ( k3_waybel_0(sK0,sK1) != a_2_0_waybel_0(sK0,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:04:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (4728)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (4727)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (4728)Refutation not found, incomplete strategy% (4728)------------------------------
% 0.21/0.53  % (4728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4722)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (4718)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.53  % (4722)# SZS output start Saturation.
% 0.21/0.53  cnf(u27,negated_conjecture,
% 0.21/0.53      r2_hidden(sK2(sK1,X0),X0) | m1_subset_1(sK2(sK1,X0),u1_struct_0(sK0)) | sK1 = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u30,negated_conjecture,
% 0.21/0.53      m1_subset_1(sK2(sK1,X0),u1_struct_0(sK0)) | sK1 = X0 | ~r2_hidden(sK2(sK1,X0),sK1)).
% 0.21/0.53  
% 0.21/0.53  % (4720)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  cnf(u22,negated_conjecture,
% 0.21/0.53      r2_hidden(sK2(X0,sK1),X0) | m1_subset_1(sK2(X0,sK1),u1_struct_0(sK0)) | sK1 = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u11,negated_conjecture,
% 0.21/0.53      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.53  
% 0.21/0.53  cnf(u16,axiom,
% 0.21/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | X0 = X1 | r2_hidden(sK2(X0,X1),X0) | m1_subset_1(sK2(X0,X1),X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u24,negated_conjecture,
% 0.21/0.53      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | sK1 = X0 | m1_subset_1(sK2(X0,sK1),u1_struct_0(sK0)) | m1_subset_1(sK2(X0,sK1),X1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u17,axiom,
% 0.21/0.53      ~m1_subset_1(X0,k1_zfmisc_1(X2)) | X0 = X1 | r2_hidden(sK2(X0,X1),X1) | m1_subset_1(sK2(X0,X1),X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u29,negated_conjecture,
% 0.21/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sK1 = X1 | m1_subset_1(sK2(sK1,X1),u1_struct_0(sK0)) | m1_subset_1(sK2(sK1,X1),X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u27,negated_conjecture,
% 0.21/0.53      r2_hidden(sK2(sK1,X0),X0) | m1_subset_1(sK2(sK1,X0),u1_struct_0(sK0)) | sK1 = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u22,negated_conjecture,
% 0.21/0.53      r2_hidden(sK2(X0,sK1),X0) | m1_subset_1(sK2(X0,sK1),u1_struct_0(sK0)) | sK1 = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u13,axiom,
% 0.21/0.53      r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X0 = X1).
% 0.21/0.53  
% 0.21/0.53  cnf(u13,axiom,
% 0.21/0.53      r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0) | X0 = X1).
% 0.21/0.53  
% 0.21/0.53  cnf(u14,axiom,
% 0.21/0.53      ~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0) | X0 = X1).
% 0.21/0.53  
% 0.21/0.53  cnf(u15,axiom,
% 0.21/0.53      ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u12,negated_conjecture,
% 0.21/0.53      k3_waybel_0(sK0,sK1) != a_2_0_waybel_0(sK0,sK1)).
% 0.21/0.53  
% 0.21/0.53  % (4722)# SZS output end Saturation.
% 0.21/0.53  % (4722)------------------------------
% 0.21/0.53  % (4722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4722)Termination reason: Satisfiable
% 0.21/0.53  
% 0.21/0.53  % (4718)Refutation not found, incomplete strategy% (4718)------------------------------
% 0.21/0.53  % (4718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4718)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4718)Memory used [KB]: 10618
% 0.21/0.53  % (4718)Time elapsed: 0.115 s
% 0.21/0.53  % (4718)------------------------------
% 0.21/0.53  % (4718)------------------------------
% 0.21/0.53  % (4722)Memory used [KB]: 6140
% 0.21/0.53  % (4722)Time elapsed: 0.090 s
% 0.21/0.53  % (4722)------------------------------
% 0.21/0.53  % (4722)------------------------------
% 0.21/0.53  % (4720)Refutation not found, incomplete strategy% (4720)------------------------------
% 0.21/0.53  % (4720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4720)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4720)Memory used [KB]: 6140
% 0.21/0.53  % (4720)Time elapsed: 0.119 s
% 0.21/0.53  % (4720)------------------------------
% 0.21/0.53  % (4720)------------------------------
% 0.21/0.54  % (4715)Success in time 0.17 s
%------------------------------------------------------------------------------
