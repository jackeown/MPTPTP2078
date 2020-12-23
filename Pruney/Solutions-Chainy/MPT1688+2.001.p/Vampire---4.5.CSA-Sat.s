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
% DateTime   : Thu Dec  3 13:17:24 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   22 (  22 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    0
%              Number of atoms          :   34 (  34 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u27,negated_conjecture,
    ( v23_waybel_0(sK2,sK0,sK1) )).

cnf(u23,negated_conjecture,
    ( ~ v23_waybel_0(sK3,sK1,sK0) )).

cnf(u25,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) )).

cnf(u20,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) )).

cnf(u31,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u29,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u30,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u28,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) )).

cnf(u21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) )).

cnf(u35,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(X2) )).

cnf(u32,axiom,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 )).

cnf(u34,axiom,
    ( ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) )).

cnf(u24,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u19,negated_conjecture,
    ( v1_funct_1(sK3) )).

cnf(u36,axiom,
    ( ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )).

cnf(u38,negated_conjecture,
    ( v1_relat_1(sK2) )).

cnf(u37,negated_conjecture,
    ( v1_relat_1(sK3) )).

cnf(u42,negated_conjecture,
    ( k10_relat_1(sK2,k3_xboole_0(X2,X3)) = k3_xboole_0(k10_relat_1(sK2,X2),k10_relat_1(sK2,X3)) )).

cnf(u41,negated_conjecture,
    ( k10_relat_1(sK3,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK3,X0),k10_relat_1(sK3,X1)) )).

cnf(u22,negated_conjecture,
    ( sK3 = k2_funct_1(sK2) )).

cnf(u33,axiom,
    ( k9_relat_1(X0,k3_xboole_0(sK4(X0),sK5(X0))) != k3_xboole_0(k9_relat_1(X0,sK4(X0)),k9_relat_1(X0,sK5(X0)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v2_funct_1(X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:54:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (16964)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.45  % (16964)Refutation not found, incomplete strategy% (16964)------------------------------
% 0.21/0.45  % (16964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (16964)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (16964)Memory used [KB]: 1535
% 0.21/0.45  % (16964)Time elapsed: 0.046 s
% 0.21/0.45  % (16964)------------------------------
% 0.21/0.45  % (16964)------------------------------
% 0.21/0.46  % (16961)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.46  % (16961)# SZS output start Saturation.
% 0.21/0.46  cnf(u27,negated_conjecture,
% 0.21/0.46      v23_waybel_0(sK2,sK0,sK1)).
% 0.21/0.46  
% 0.21/0.46  cnf(u23,negated_conjecture,
% 0.21/0.46      ~v23_waybel_0(sK3,sK1,sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u25,negated_conjecture,
% 0.21/0.46      v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))).
% 0.21/0.46  
% 0.21/0.46  cnf(u20,negated_conjecture,
% 0.21/0.46      v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))).
% 0.21/0.46  
% 0.21/0.46  cnf(u31,negated_conjecture,
% 0.21/0.46      l1_orders_2(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u29,negated_conjecture,
% 0.21/0.46      l1_orders_2(sK1)).
% 0.21/0.46  
% 0.21/0.46  cnf(u30,negated_conjecture,
% 0.21/0.46      ~v2_struct_0(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u28,negated_conjecture,
% 0.21/0.46      ~v2_struct_0(sK1)).
% 0.21/0.46  
% 0.21/0.46  cnf(u26,negated_conjecture,
% 0.21/0.46      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))).
% 0.21/0.46  
% 0.21/0.46  cnf(u21,negated_conjecture,
% 0.21/0.46      m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))).
% 0.21/0.46  
% 0.21/0.46  cnf(u35,axiom,
% 0.21/0.46      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)).
% 0.21/0.46  
% 0.21/0.46  cnf(u32,axiom,
% 0.21/0.46      ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0).
% 0.21/0.46  
% 0.21/0.46  cnf(u34,axiom,
% 0.21/0.46      ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u24,negated_conjecture,
% 0.21/0.46      v1_funct_1(sK2)).
% 0.21/0.46  
% 0.21/0.46  cnf(u19,negated_conjecture,
% 0.21/0.46      v1_funct_1(sK3)).
% 0.21/0.46  
% 0.21/0.46  cnf(u36,axiom,
% 0.21/0.46      ~v1_funct_1(X2) | ~v1_relat_1(X2) | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))).
% 0.21/0.46  
% 0.21/0.46  cnf(u38,negated_conjecture,
% 0.21/0.46      v1_relat_1(sK2)).
% 0.21/0.46  
% 0.21/0.46  cnf(u37,negated_conjecture,
% 0.21/0.46      v1_relat_1(sK3)).
% 0.21/0.46  
% 0.21/0.46  cnf(u42,negated_conjecture,
% 0.21/0.46      k10_relat_1(sK2,k3_xboole_0(X2,X3)) = k3_xboole_0(k10_relat_1(sK2,X2),k10_relat_1(sK2,X3))).
% 0.21/0.46  
% 0.21/0.46  cnf(u41,negated_conjecture,
% 0.21/0.46      k10_relat_1(sK3,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK3,X0),k10_relat_1(sK3,X1))).
% 0.21/0.46  
% 0.21/0.46  cnf(u22,negated_conjecture,
% 0.21/0.46      sK3 = k2_funct_1(sK2)).
% 0.21/0.46  
% 0.21/0.46  cnf(u33,axiom,
% 0.21/0.46      k9_relat_1(X0,k3_xboole_0(sK4(X0),sK5(X0))) != k3_xboole_0(k9_relat_1(X0,sK4(X0)),k9_relat_1(X0,sK5(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)).
% 0.21/0.46  
% 0.21/0.46  % (16961)# SZS output end Saturation.
% 0.21/0.46  % (16961)------------------------------
% 0.21/0.46  % (16961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (16961)Termination reason: Satisfiable
% 0.21/0.46  
% 0.21/0.46  % (16961)Memory used [KB]: 6140
% 0.21/0.46  % (16961)Time elapsed: 0.033 s
% 0.21/0.46  % (16961)------------------------------
% 0.21/0.46  % (16961)------------------------------
% 0.21/0.46  % (16947)Success in time 0.095 s
%------------------------------------------------------------------------------
