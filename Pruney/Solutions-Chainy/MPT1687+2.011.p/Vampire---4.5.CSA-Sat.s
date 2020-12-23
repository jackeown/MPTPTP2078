%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:21 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   36 (  36 expanded)
%              Number of leaves         :   36 (  36 expanded)
%              Depth                    :    0
%              Number of atoms          :   65 (  65 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u42,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u40,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u45,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u65,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u64,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u41,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u39,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u88,negated_conjecture,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

cnf(u89,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

cnf(u96,negated_conjecture,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

cnf(u63,axiom,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0
    | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) )).

cnf(u59,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
    | ~ v1_funct_2(X2,k1_xboole_0,X1) )).

cnf(u60,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
    | v1_funct_2(X2,k1_xboole_0,X1) )).

cnf(u61,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | ~ v1_funct_2(X2,X0,k1_xboole_0) )).

cnf(u49,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(X2) )).

cnf(u52,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v4_relat_1(X2,X0) )).

cnf(u50,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) )).

cnf(u51,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) )).

cnf(u57,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1
    | k1_relset_1(X0,X1,X2) != X0
    | v1_funct_2(X2,X0,X1) )).

cnf(u58,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1
    | k1_relset_1(X0,X1,X2) = X0
    | ~ v1_funct_2(X2,X0,X1) )).

cnf(u36,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u90,negated_conjecture,
    ( v4_relat_1(sK2,k1_relat_1(sK2)) )).

cnf(u48,axiom,
    ( ~ v4_relat_1(X1,X0)
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = X1 )).

cnf(u66,negated_conjecture,
    ( v1_relat_1(sK2) )).

cnf(u44,axiom,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) )).

cnf(u47,axiom,
    ( ~ v1_relat_1(X1)
    | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )).

cnf(u43,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u106,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(sK2)) )).

cnf(u46,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u93,negated_conjecture,
    ( sK2 = k7_relat_1(sK2,k1_relat_1(sK2)) )).

cnf(u86,negated_conjecture,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) )).

cnf(u75,negated_conjecture,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) )).

cnf(u91,negated_conjecture,
    ( k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) )).

cnf(u107,negated_conjecture,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) )).

cnf(u74,negated_conjecture,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) )).

cnf(u92,negated_conjecture,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:59:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (15113)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.44  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.44  % (15113)# SZS output start Saturation.
% 0.22/0.44  cnf(u42,negated_conjecture,
% 0.22/0.44      l1_orders_2(sK0)).
% 0.22/0.44  
% 0.22/0.44  cnf(u40,negated_conjecture,
% 0.22/0.44      l1_orders_2(sK1)).
% 0.22/0.44  
% 0.22/0.44  cnf(u45,axiom,
% 0.22/0.44      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.22/0.44  
% 0.22/0.44  cnf(u65,negated_conjecture,
% 0.22/0.44      l1_struct_0(sK0)).
% 0.22/0.44  
% 0.22/0.44  cnf(u64,negated_conjecture,
% 0.22/0.44      l1_struct_0(sK1)).
% 0.22/0.44  
% 0.22/0.44  cnf(u41,negated_conjecture,
% 0.22/0.44      ~v2_struct_0(sK0)).
% 0.22/0.44  
% 0.22/0.44  cnf(u39,negated_conjecture,
% 0.22/0.44      ~v2_struct_0(sK1)).
% 0.22/0.44  
% 0.22/0.44  cnf(u88,negated_conjecture,
% 0.22/0.44      v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))).
% 0.22/0.44  
% 0.22/0.44  cnf(u89,negated_conjecture,
% 0.22/0.44      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 0.22/0.44  
% 0.22/0.44  cnf(u96,negated_conjecture,
% 0.22/0.44      ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))).
% 0.22/0.44  
% 0.22/0.44  cnf(u63,axiom,
% 0.22/0.44      ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)).
% 0.22/0.44  
% 0.22/0.44  cnf(u59,axiom,
% 0.22/0.44      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)).
% 0.22/0.44  
% 0.22/0.44  cnf(u60,axiom,
% 0.22/0.44      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)).
% 0.22/0.44  
% 0.22/0.44  cnf(u61,axiom,
% 0.22/0.44      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)).
% 0.22/0.44  
% 0.22/0.44  cnf(u49,axiom,
% 0.22/0.44      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)).
% 0.22/0.44  
% 0.22/0.44  cnf(u52,axiom,
% 0.22/0.44      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)).
% 0.22/0.44  
% 0.22/0.44  cnf(u50,axiom,
% 0.22/0.44      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)).
% 0.22/0.44  
% 0.22/0.44  cnf(u51,axiom,
% 0.22/0.44      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)).
% 0.22/0.44  
% 0.22/0.44  cnf(u57,axiom,
% 0.22/0.44      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)).
% 0.22/0.44  
% 0.22/0.44  cnf(u58,axiom,
% 0.22/0.44      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)).
% 0.22/0.44  
% 0.22/0.44  cnf(u36,negated_conjecture,
% 0.22/0.44      v1_funct_1(sK2)).
% 0.22/0.44  
% 0.22/0.44  cnf(u90,negated_conjecture,
% 0.22/0.44      v4_relat_1(sK2,k1_relat_1(sK2))).
% 0.22/0.44  
% 0.22/0.44  cnf(u48,axiom,
% 0.22/0.44      ~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1).
% 0.22/0.44  
% 0.22/0.44  cnf(u66,negated_conjecture,
% 0.22/0.44      v1_relat_1(sK2)).
% 0.22/0.44  
% 0.22/0.44  cnf(u44,axiom,
% 0.22/0.44      ~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)).
% 0.22/0.44  
% 0.22/0.44  cnf(u47,axiom,
% 0.22/0.44      ~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)).
% 0.22/0.44  
% 0.22/0.44  cnf(u43,axiom,
% 0.22/0.44      v1_xboole_0(k1_xboole_0)).
% 0.22/0.44  
% 0.22/0.44  cnf(u106,negated_conjecture,
% 0.22/0.44      ~v1_xboole_0(k1_relat_1(sK2))).
% 0.22/0.44  
% 0.22/0.44  cnf(u46,axiom,
% 0.22/0.44      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.22/0.44  
% 0.22/0.44  cnf(u93,negated_conjecture,
% 0.22/0.44      sK2 = k7_relat_1(sK2,k1_relat_1(sK2))).
% 0.22/0.44  
% 0.22/0.44  cnf(u86,negated_conjecture,
% 0.22/0.44      u1_struct_0(sK0) = k1_relat_1(sK2)).
% 0.22/0.44  
% 0.22/0.44  cnf(u75,negated_conjecture,
% 0.22/0.44      k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))).
% 0.22/0.44  
% 0.22/0.44  cnf(u91,negated_conjecture,
% 0.22/0.44      k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)).
% 0.22/0.44  
% 0.22/0.44  cnf(u107,negated_conjecture,
% 0.22/0.44      k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))).
% 0.22/0.44  
% 0.22/0.44  cnf(u74,negated_conjecture,
% 0.22/0.44      k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)).
% 0.22/0.44  
% 0.22/0.44  cnf(u92,negated_conjecture,
% 0.22/0.44      k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)).
% 0.22/0.44  
% 0.22/0.44  % (15113)# SZS output end Saturation.
% 0.22/0.44  % (15113)------------------------------
% 0.22/0.44  % (15113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (15113)Termination reason: Satisfiable
% 0.22/0.44  
% 0.22/0.44  % (15113)Memory used [KB]: 1663
% 0.22/0.44  % (15113)Time elapsed: 0.029 s
% 0.22/0.44  % (15113)------------------------------
% 0.22/0.44  % (15113)------------------------------
% 0.22/0.44  % (15095)Success in time 0.082 s
%------------------------------------------------------------------------------
