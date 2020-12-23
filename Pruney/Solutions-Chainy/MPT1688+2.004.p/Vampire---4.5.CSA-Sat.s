%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:24 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   21 (  21 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    0
%              Number of atoms          :   35 (  35 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u21,negated_conjecture,
    ( v23_waybel_0(sK2,sK0,sK1) )).

cnf(u17,negated_conjecture,
    ( ~ v23_waybel_0(sK3,sK1,sK0) )).

cnf(u19,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) )).

cnf(u14,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) )).

cnf(u25,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u23,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u24,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u22,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) )).

cnf(u15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) )).

cnf(u28,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(X2) )).

cnf(u26,axiom,
    ( v2_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) )).

cnf(u27,axiom,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 )).

cnf(u33,negated_conjecture,
    ( ~ v2_funct_1(sK2)
    | v2_funct_1(sK3) )).

cnf(u39,negated_conjecture,
    ( ~ v2_funct_1(sK2)
    | sK3 = k2_funct_1(k2_funct_1(sK3)) )).

cnf(u18,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u13,negated_conjecture,
    ( v1_funct_1(sK3) )).

cnf(u34,axiom,
    ( ~ v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(k2_funct_1(X0))
    | k2_funct_1(X0) = k2_funct_1(k2_funct_1(k2_funct_1(X0)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) )).

cnf(u30,negated_conjecture,
    ( v1_relat_1(sK2) )).

cnf(u29,negated_conjecture,
    ( v1_relat_1(sK3) )).

cnf(u16,negated_conjecture,
    ( sK3 = k2_funct_1(sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:29:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (18131)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.48  % (18139)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.48  % (18131)# SZS output start Saturation.
% 0.21/0.48  cnf(u21,negated_conjecture,
% 0.21/0.48      v23_waybel_0(sK2,sK0,sK1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u17,negated_conjecture,
% 0.21/0.48      ~v23_waybel_0(sK3,sK1,sK0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u19,negated_conjecture,
% 0.21/0.48      v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))).
% 0.21/0.48  
% 0.21/0.48  cnf(u14,negated_conjecture,
% 0.21/0.48      v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))).
% 0.21/0.48  
% 0.21/0.48  cnf(u25,negated_conjecture,
% 0.21/0.48      l1_orders_2(sK0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u23,negated_conjecture,
% 0.21/0.48      l1_orders_2(sK1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u24,negated_conjecture,
% 0.21/0.48      ~v2_struct_0(sK0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u22,negated_conjecture,
% 0.21/0.48      ~v2_struct_0(sK1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u20,negated_conjecture,
% 0.21/0.48      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))).
% 0.21/0.48  
% 0.21/0.48  cnf(u15,negated_conjecture,
% 0.21/0.48      m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))).
% 0.21/0.48  
% 0.21/0.48  cnf(u28,axiom,
% 0.21/0.48      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)).
% 0.21/0.48  
% 0.21/0.48  cnf(u26,axiom,
% 0.21/0.48      v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u27,axiom,
% 0.21/0.48      ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0).
% 0.21/0.48  
% 0.21/0.48  cnf(u33,negated_conjecture,
% 0.21/0.48      ~v2_funct_1(sK2) | v2_funct_1(sK3)).
% 0.21/0.48  
% 0.21/0.48  cnf(u39,negated_conjecture,
% 0.21/0.48      ~v2_funct_1(sK2) | sK3 = k2_funct_1(k2_funct_1(sK3))).
% 0.21/0.48  
% 0.21/0.48  cnf(u18,negated_conjecture,
% 0.21/0.48      v1_funct_1(sK2)).
% 0.21/0.48  
% 0.21/0.48  cnf(u13,negated_conjecture,
% 0.21/0.48      v1_funct_1(sK3)).
% 0.21/0.48  
% 0.21/0.48  cnf(u34,axiom,
% 0.21/0.48      ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | k2_funct_1(X0) = k2_funct_1(k2_funct_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u30,negated_conjecture,
% 0.21/0.48      v1_relat_1(sK2)).
% 0.21/0.48  
% 0.21/0.48  cnf(u29,negated_conjecture,
% 0.21/0.48      v1_relat_1(sK3)).
% 0.21/0.48  
% 0.21/0.48  cnf(u16,negated_conjecture,
% 0.21/0.48      sK3 = k2_funct_1(sK2)).
% 0.21/0.48  
% 0.21/0.48  % (18131)# SZS output end Saturation.
% 0.21/0.48  % (18131)------------------------------
% 0.21/0.48  % (18131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (18131)Termination reason: Satisfiable
% 0.21/0.48  
% 0.21/0.48  % (18131)Memory used [KB]: 6140
% 0.21/0.48  % (18131)Time elapsed: 0.065 s
% 0.21/0.48  % (18131)------------------------------
% 0.21/0.48  % (18131)------------------------------
% 0.21/0.48  % (18117)Success in time 0.128 s
%------------------------------------------------------------------------------
