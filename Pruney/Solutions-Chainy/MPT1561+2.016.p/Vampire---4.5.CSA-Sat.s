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
% DateTime   : Thu Dec  3 13:16:10 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 1.33s
% Verified   : 
% Statistics : Number of clauses        :  112 ( 112 expanded)
%              Number of leaves         :  112 ( 112 expanded)
%              Depth                    :    0
%              Number of atoms          :  391 ( 391 expanded)
%              Number of equality atoms :   85 (  85 expanded)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u231,negated_conjecture,
    ( r2_lattice3(sK0,X4,sK2(sK0,k1_tarski(sK1),sK1))
    | r2_hidden(sK2(sK0,X4,sK2(sK0,k1_tarski(sK1),sK1)),X4)
    | r2_hidden(sK1,sK3(sK0,sK1,sK1)) )).

cnf(u230,negated_conjecture,
    ( r2_lattice3(sK0,X3,sK2(sK0,k1_tarski(sK1),sK1))
    | m1_subset_1(sK2(sK0,X3,sK2(sK0,k1_tarski(sK1),sK1)),u1_struct_0(sK0))
    | r2_hidden(sK1,sK3(sK0,sK1,sK1)) )).

cnf(u243,negated_conjecture,
    ( r2_lattice3(sK0,X4,sK2(sK0,k1_tarski(sK1),sK1))
    | r2_hidden(sK2(sK0,X4,sK2(sK0,k1_tarski(sK1),sK1)),X4)
    | m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u242,negated_conjecture,
    ( r2_lattice3(sK0,X3,sK2(sK0,k1_tarski(sK1),sK1))
    | m1_subset_1(sK2(sK0,X3,sK2(sK0,k1_tarski(sK1),sK1)),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u81,negated_conjecture,
    ( r2_lattice3(sK0,X0,sK1)
    | r2_hidden(sK2(sK0,X0,sK1),X0) )).

cnf(u86,negated_conjecture,
    ( r2_lattice3(sK0,X0,sK1)
    | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0)) )).

% (2516)Refutation not found, incomplete strategy% (2516)------------------------------
% (2516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2516)Termination reason: Refutation not found, incomplete strategy

% (2516)Memory used [KB]: 1791
% (2516)Time elapsed: 0.135 s
% (2516)------------------------------
% (2516)------------------------------
cnf(u49,axiom,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | r1_orders_2(X0,X4,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u225,negated_conjecture,
    ( v6_orders_2(k6_domain_1(u1_struct_0(sK0),sK2(sK0,k1_tarski(sK1),sK1)),sK0)
    | r2_hidden(sK1,sK3(sK0,sK1,sK1)) )).

cnf(u237,negated_conjecture,
    ( v6_orders_2(k6_domain_1(u1_struct_0(sK0),sK2(sK0,k1_tarski(sK1),sK1)),sK0)
    | m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u163,negated_conjecture,
    ( v6_orders_2(sK3(sK0,sK1,sK1),sK0)
    | r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),k1_tarski(sK1)) )).

cnf(u198,negated_conjecture,
    ( v6_orders_2(sK3(sK0,sK1,sK1),sK0)
    | m1_subset_1(sK2(sK0,k1_tarski(sK1),sK1),u1_struct_0(sK0)) )).

cnf(u373,negated_conjecture,
    ( v6_orders_2(sK3(sK0,sK1,sK1),sK0) )).

cnf(u115,negated_conjecture,
    ( v6_orders_2(k1_tarski(sK1),sK0) )).

cnf(u57,axiom,
    ( ~ v6_orders_2(X4,X0)
    | r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
    | r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) )).

cnf(u42,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u65,axiom,
    ( ~ v3_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_hidden(X2,sK3(X0,X1,X2)) )).

cnf(u64,axiom,
    ( ~ v3_orders_2(X0)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_hidden(X2,sK3(X0,X1,X2)) )).

cnf(u63,axiom,
    ( ~ v3_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_hidden(X1,sK3(X0,X1,X2)) )).

cnf(u62,axiom,
    ( ~ v3_orders_2(X0)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_hidden(X1,sK3(X0,X1,X2)) )).

% (2507)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
cnf(u61,axiom,
    ( ~ v3_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )).

cnf(u60,axiom,
    ( ~ v3_orders_2(X0)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )).

cnf(u59,axiom,
    ( ~ v3_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v6_orders_2(sK3(X0,X1,X2),X0) )).

cnf(u58,axiom,
    ( ~ v3_orders_2(X0)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v6_orders_2(sK3(X0,X1,X2),X0) )).

cnf(u55,axiom,
    ( ~ v3_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0) )).

cnf(u54,axiom,
    ( ~ v3_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | v2_struct_0(X0) )).

cnf(u250,negated_conjecture,
    ( r1_orders_2(sK0,sK2(sK0,k1_tarski(sK1),sK1),sK1)
    | r1_orders_2(sK0,sK1,sK2(sK0,k1_tarski(sK1),sK1))
    | r2_hidden(sK1,sK3(sK0,sK1,sK1)) )).

cnf(u249,negated_conjecture,
    ( r1_orders_2(sK0,sK2(sK0,k1_tarski(sK1),sK1),sK1)
    | r1_orders_2(sK0,sK1,sK2(sK0,k1_tarski(sK1),sK1))
    | m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u144,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1)
    | r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),k1_tarski(sK1)) )).

cnf(u166,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1)
    | m1_subset_1(sK2(sK0,k1_tarski(sK1),sK1),u1_struct_0(sK0)) )).

cnf(u248,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1) )).

cnf(u110,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,X1,X0),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u108,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u106,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(X0,sK3(sK0,X1,X0)) )).

cnf(u104,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r2_hidden(X1,sK3(sK0,X0,X1)) )).

cnf(u102,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(X1,sK3(sK0,X1,X0)) )).

cnf(u100,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r2_hidden(X0,sK3(sK0,X0,X1)) )).

cnf(u98,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | v6_orders_2(sK3(sK0,X1,X0),sK0) )).

cnf(u96,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | v6_orders_2(sK3(sK0,X0,X1),sK0) )).

cnf(u56,axiom,
    ( ~ r1_orders_2(X0,X2,X1)
    | X1 = X2
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) )).

cnf(u52,axiom,
    ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u43,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u165,negated_conjecture,
    ( m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),k1_tarski(sK1)) )).

cnf(u240,negated_conjecture,
    ( m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tarski(sK2(sK0,k1_tarski(sK1),sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK0,k1_tarski(sK1),sK1))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u375,negated_conjecture,
    ( m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u199,negated_conjecture,
    ( m1_subset_1(sK2(sK0,k1_tarski(sK1),sK1),u1_struct_0(sK0))
    | r2_hidden(sK1,sK3(sK0,sK1,sK1)) )).

cnf(u200,negated_conjecture,
    ( m1_subset_1(sK2(sK0,k1_tarski(sK1),sK1),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u45,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u224,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,k1_tarski(sK1),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,sK3(sK0,sK1,sK1)) )).

cnf(u236,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,k1_tarski(sK1),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u123,negated_conjecture,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u121,negated_conjecture,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(X1,k1_tarski(sK1))
    | ~ r2_hidden(X0,k1_tarski(sK1))
    | r1_orders_2(sK0,X0,X1)
    | r1_orders_2(sK0,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u503,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,X0)
    | r1_orders_2(sK0,X0,sK1)
    | ~ r2_hidden(X0,sK3(sK0,sK1,sK1)) )).

cnf(u445,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r2_hidden(X0,sK3(sK0,sK1,sK1))
    | r1_orders_2(sK0,sK1,X0)
    | m1_subset_1(sK2(sK0,k1_tarski(sK1),sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,sK1) )).

cnf(u441,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r2_hidden(X0,sK3(sK0,sK1,sK1))
    | r1_orders_2(sK0,sK1,X0)
    | r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),k1_tarski(sK1))
    | r1_orders_2(sK0,X0,sK1) )).

cnf(u397,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,sK3(sK0,sK1,sK1))
    | ~ r2_hidden(X0,sK3(sK0,sK1,sK1))
    | r1_orders_2(sK0,X1,X0)
    | r1_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u241,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r2_hidden(X0,k1_tarski(sK1))
    | r1_orders_2(sK0,X0,sK2(sK0,k1_tarski(sK1),sK1))
    | r1_orders_2(sK0,sK2(sK0,k1_tarski(sK1),sK1),X0)
    | m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u229,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r2_hidden(X0,k1_tarski(sK1))
    | r1_orders_2(sK0,X0,sK2(sK0,k1_tarski(sK1),sK1))
    | r1_orders_2(sK0,sK2(sK0,k1_tarski(sK1),sK1),X0)
    | r2_hidden(sK1,sK3(sK0,sK1,sK1)) )).

cnf(u220,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,X1)
    | ~ r2_hidden(X1,sK3(sK0,sK1,sK1))
    | ~ r2_hidden(X0,sK3(sK0,sK1,sK1))
    | r1_orders_2(sK0,X1,X0)
    | m1_subset_1(sK2(sK0,k1_tarski(sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u214,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,X1)
    | ~ r2_hidden(X1,sK3(sK0,sK1,sK1))
    | ~ r2_hidden(X0,sK3(sK0,sK1,sK1))
    | r1_orders_2(sK0,X1,X0)
    | r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),k1_tarski(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u202,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,sK1)
    | r1_orders_2(sK0,sK1,X0)
    | ~ r2_hidden(X0,k1_tarski(sK1)) )).

cnf(u167,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r2_hidden(X1,k1_tarski(sK1))
    | r1_orders_2(sK0,X1,X0)
    | r1_orders_2(sK0,X0,X1)
    | ~ r2_hidden(X0,k1_tarski(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK0)) )).

cnf(u118,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,X0)
    | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,X1,sK1) )).

cnf(u113,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(sK2(sK0,X0,sK1),X0)
    | r1_orders_2(sK0,X1,sK1) )).

% (2519)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
cnf(u94,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u84,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | v6_orders_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) )).

cnf(u51,axiom,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | r2_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0) )).

cnf(u50,axiom,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | r2_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0) )).

cnf(u66,axiom,
    ( ~ m1_subset_1(X1,X0)
    | k6_domain_1(X0,X1) = k1_tarski(X1)
    | v1_xboole_0(X0) )).

cnf(u44,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u48,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u228,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_tarski(sK2(sK0,k1_tarski(sK1),sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK0,k1_tarski(sK1),sK1))
    | r2_hidden(sK1,sK3(sK0,sK1,sK1)) )).

cnf(u124,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)) = k1_tarski(k1_tarski(sK1)) )).

cnf(u232,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK3(sK0,sK1,sK1)) = k1_tarski(sK3(sK0,sK1,sK1))
    | r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),k1_tarski(sK1)) )).

cnf(u411,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK3(sK0,sK1,sK1)) = k1_tarski(sK3(sK0,sK1,sK1))
    | k1_tarski(sK2(sK0,k1_tarski(sK1),sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK0,k1_tarski(sK1),sK1)) )).

cnf(u446,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK3(sK0,sK1,sK1)) = k1_tarski(sK3(sK0,sK1,sK1)) )).

cnf(u53,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u74,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u41,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u69,axiom,
    ( r2_hidden(sK4(X0,X1),X1)
    | sK4(X0,X1) = X0
    | k1_tarski(X0) = X1 )).

cnf(u164,negated_conjecture,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),k1_tarski(sK1))
    | r2_hidden(sK1,sK3(sK0,sK1,sK1)) )).

cnf(u216,negated_conjecture,
    ( r2_hidden(sK1,sK3(sK0,sK1,sK1))
    | sK1 = sK2(sK0,k1_tarski(sK1),sK1) )).

cnf(u215,negated_conjecture,
    ( r2_hidden(sK1,sK3(sK0,sK1,sK1))
    | k1_tarski(sK1) = k1_tarski(sK2(sK0,k1_tarski(sK1),sK1))
    | sK1 = sK4(sK2(sK0,k1_tarski(sK1),sK1),k1_tarski(sK1)) )).

cnf(u374,negated_conjecture,
    ( r2_hidden(sK1,sK3(sK0,sK1,sK1)) )).

cnf(u253,negated_conjecture,
    ( r2_hidden(sK1,sK3(sK0,sK1,sK1))
    | sK4(X5,k1_tarski(sK1)) = X5
    | k1_tarski(sK1) = k1_tarski(X5)
    | sK2(sK0,k1_tarski(sK1),sK1) = sK4(X5,k1_tarski(sK1)) )).

cnf(u257,negated_conjecture,
    ( r2_hidden(sK1,sK3(sK0,sK1,sK1))
    | sK4(sK2(sK0,k1_tarski(sK1),sK1),k1_tarski(sK1)) = sK4(X5,k1_tarski(sK1))
    | sK4(X5,k1_tarski(sK1)) = X5
    | k1_tarski(sK1) = k1_tarski(X5)
    | k1_tarski(sK1) = k1_tarski(sK2(sK0,k1_tarski(sK1),sK1)) )).

cnf(u72,axiom,
    ( r2_hidden(X3,k1_tarski(X3)) )).

cnf(u354,axiom,
    ( ~ r2_hidden(sK4(X14,k1_tarski(X13)),k1_tarski(X13))
    | sK4(X14,k1_tarski(X13)) != X12
    | k1_tarski(X12) = k1_tarski(X13)
    | sK4(X12,k1_tarski(X13)) = X12
    | k1_tarski(X13) = k1_tarski(X14) )).

cnf(u70,axiom,
    ( ~ r2_hidden(sK4(X0,X1),X1)
    | sK4(X0,X1) != X0
    | k1_tarski(X0) = X1 )).

cnf(u223,negated_conjecture,
    ( ~ r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),X2)
    | r2_hidden(sK1,sK3(sK0,sK1,sK1))
    | r2_hidden(sK2(sK0,X2,sK1),X2)
    | r1_orders_2(sK0,sK2(sK0,k1_tarski(sK1),sK1),sK1) )).

cnf(u222,negated_conjecture,
    ( ~ r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),X1)
    | r2_hidden(sK1,sK3(sK0,sK1,sK1))
    | m1_subset_1(sK2(sK0,X1,sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2(sK0,k1_tarski(sK1),sK1),sK1) )).

cnf(u235,negated_conjecture,
    ( ~ r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),X2)
    | m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2(sK0,X2,sK1),X2)
    | r1_orders_2(sK0,sK2(sK0,k1_tarski(sK1),sK1),sK1) )).

cnf(u234,negated_conjecture,
    ( ~ r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),X1)
    | m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2(sK0,X1,sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2(sK0,k1_tarski(sK1),sK1),sK1) )).

cnf(u138,negated_conjecture,
    ( ~ r2_hidden(sK1,X0)
    | r2_hidden(sK2(sK0,X0,sK1),X0)
    | r1_orders_2(sK0,sK1,sK1) )).

cnf(u139,negated_conjecture,
    ( ~ r2_hidden(sK1,X0)
    | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK1) )).

cnf(u73,axiom,
    ( ~ r2_hidden(X3,k1_tarski(X0))
    | X0 = X3 )).

cnf(u136,axiom,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | k1_tarski(X0) = k1_tarski(X1)
    | sK4(X0,k1_tarski(X1)) = X1 )).

cnf(u206,axiom,
    ( ~ r2_hidden(X4,k1_tarski(X3))
    | sK4(X2,k1_tarski(X3)) = X4
    | sK4(X2,k1_tarski(X3)) = X2
    | k1_tarski(X3) = k1_tarski(X2) )).

cnf(u209,axiom,
    ( ~ r2_hidden(X13,k1_tarski(X12))
    | k1_tarski(X12) = k1_tarski(X13)
    | sK4(X11,k1_tarski(X12)) = sK4(X13,k1_tarski(X12))
    | sK4(X11,k1_tarski(X12)) = X11
    | k1_tarski(X12) = k1_tarski(X11) )).

cnf(u143,axiom,
    ( sK4(sK4(X1,k1_tarski(X2)),k1_tarski(X2)) = X2
    | k1_tarski(X2) = k1_tarski(sK4(X1,k1_tarski(X2)))
    | sK4(X1,k1_tarski(X2)) = X1
    | k1_tarski(X1) = k1_tarski(X2) )).

cnf(u207,axiom,
    ( sK4(X7,k1_tarski(X6)) = X7
    | sK4(X5,k1_tarski(X6)) = sK4(X7,k1_tarski(X6))
    | sK4(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u77,axiom,
    ( sK4(X0,k1_tarski(X1)) = X0
    | sK4(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u77_001,axiom,
    ( sK4(X0,k1_tarski(X1)) = X0
    | sK4(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u207_002,axiom,
    ( sK4(X7,k1_tarski(X6)) = X7
    | sK4(X5,k1_tarski(X6)) = sK4(X7,k1_tarski(X6))
    | sK4(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u207_003,axiom,
    ( sK4(X7,k1_tarski(X6)) = X7
    | sK4(X5,k1_tarski(X6)) = sK4(X7,k1_tarski(X6))
    | sK4(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u89,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) )).

cnf(u179,axiom,
    ( k1_tarski(X5) = k1_tarski(sK4(X4,k1_tarski(X5)))
    | sK4(X4,k1_tarski(X5)) = X4
    | k1_tarski(X5) = k1_tarski(X4) )).

cnf(u47,axiom,
    ( k1_tarski(X0) = k2_tarski(X0,X0) )).

cnf(u312,axiom,
    ( sK4(X2,k1_tarski(X1)) != X0
    | sK4(X2,k1_tarski(X1)) = X2
    | sK4(X0,k1_tarski(X1)) = X0
    | k1_tarski(X1) = k1_tarski(X2)
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u310,axiom,
    ( sK4(X2,k1_tarski(X1)) != X0
    | sK4(X0,k1_tarski(X1)) = sK4(X2,k1_tarski(X1))
    | sK4(X2,k1_tarski(X1)) = X2
    | k1_tarski(X0) = k1_tarski(X1)
    | k1_tarski(X1) = k1_tarski(X2) )).

cnf(u131,axiom,
    ( X0 != X1
    | sK4(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u137,axiom,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1)
    | sK4(X0,k1_tarski(X1)) = X0 )).

cnf(u91,negated_conjecture,
    ( sK1 != k2_yellow_0(sK0,k1_tarski(sK1))
    | sK1 != k1_yellow_0(sK0,k1_tarski(sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n018.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 17:20:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (2505)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.50  % (2517)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.51  % (2498)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (2521)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (2502)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (2510)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (2510)Refutation not found, incomplete strategy% (2510)------------------------------
% 0.21/0.52  % (2510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2510)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2510)Memory used [KB]: 10618
% 0.21/0.52  % (2510)Time elapsed: 0.109 s
% 0.21/0.52  % (2510)------------------------------
% 0.21/0.52  % (2510)------------------------------
% 0.21/0.52  % (2509)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (2508)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (2511)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (2500)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (2508)Refutation not found, incomplete strategy% (2508)------------------------------
% 0.21/0.52  % (2508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2513)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (2526)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (2520)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (2514)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.53  % (2515)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (2527)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (2527)Refutation not found, incomplete strategy% (2527)------------------------------
% 0.21/0.53  % (2527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2526)Refutation not found, incomplete strategy% (2526)------------------------------
% 0.21/0.53  % (2526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2527)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2527)Memory used [KB]: 1663
% 0.21/0.53  % (2527)Time elapsed: 0.003 s
% 0.21/0.53  % (2527)------------------------------
% 0.21/0.53  % (2527)------------------------------
% 0.21/0.53  % (2516)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (2526)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2526)Memory used [KB]: 10746
% 0.21/0.53  % (2526)Time elapsed: 0.125 s
% 0.21/0.53  % (2526)------------------------------
% 0.21/0.53  % (2526)------------------------------
% 0.21/0.53  % (2515)Refutation not found, incomplete strategy% (2515)------------------------------
% 0.21/0.53  % (2515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2515)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2515)Memory used [KB]: 1791
% 0.21/0.53  % (2515)Time elapsed: 0.122 s
% 0.21/0.53  % (2515)------------------------------
% 0.21/0.53  % (2515)------------------------------
% 0.21/0.53  % (2522)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (2499)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (2499)Refutation not found, incomplete strategy% (2499)------------------------------
% 0.21/0.53  % (2499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2499)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2499)Memory used [KB]: 1663
% 0.21/0.53  % (2499)Time elapsed: 0.129 s
% 0.21/0.53  % (2499)------------------------------
% 0.21/0.53  % (2499)------------------------------
% 0.21/0.53  % (2502)Refutation not found, incomplete strategy% (2502)------------------------------
% 0.21/0.53  % (2502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (2502)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (2502)Memory used [KB]: 1791
% 1.33/0.53  % (2502)Time elapsed: 0.121 s
% 1.33/0.53  % (2502)------------------------------
% 1.33/0.53  % (2502)------------------------------
% 1.33/0.54  % (2501)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.33/0.54  % (2512)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.33/0.54  % (2503)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.33/0.54  % (2523)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.33/0.54  % (2518)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.33/0.54  % (2504)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.54  % (2523)Refutation not found, incomplete strategy% (2523)------------------------------
% 1.33/0.54  % (2523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (2523)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (2523)Memory used [KB]: 6268
% 1.33/0.54  % (2523)Time elapsed: 0.131 s
% 1.33/0.54  % (2523)------------------------------
% 1.33/0.54  % (2523)------------------------------
% 1.33/0.54  % (2508)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (2508)Memory used [KB]: 10746
% 1.33/0.54  % (2508)Time elapsed: 0.108 s
% 1.33/0.54  % (2508)------------------------------
% 1.33/0.54  % (2508)------------------------------
% 1.33/0.54  % (2506)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.33/0.54  % (2514)Refutation not found, incomplete strategy% (2514)------------------------------
% 1.33/0.54  % (2514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (2524)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.33/0.54  % (2514)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (2514)Memory used [KB]: 10746
% 1.33/0.54  % (2514)Time elapsed: 0.141 s
% 1.33/0.54  % (2514)------------------------------
% 1.33/0.54  % (2514)------------------------------
% 1.33/0.55  % (2524)Refutation not found, incomplete strategy% (2524)------------------------------
% 1.33/0.55  % (2524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (2524)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (2524)Memory used [KB]: 6268
% 1.33/0.55  % (2524)Time elapsed: 0.141 s
% 1.33/0.55  % (2524)------------------------------
% 1.33/0.55  % (2524)------------------------------
% 1.33/0.55  % (2505)# SZS output start Saturation.
% 1.33/0.55  cnf(u231,negated_conjecture,
% 1.33/0.55      r2_lattice3(sK0,X4,sK2(sK0,k1_tarski(sK1),sK1)) | r2_hidden(sK2(sK0,X4,sK2(sK0,k1_tarski(sK1),sK1)),X4) | r2_hidden(sK1,sK3(sK0,sK1,sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u230,negated_conjecture,
% 1.33/0.55      r2_lattice3(sK0,X3,sK2(sK0,k1_tarski(sK1),sK1)) | m1_subset_1(sK2(sK0,X3,sK2(sK0,k1_tarski(sK1),sK1)),u1_struct_0(sK0)) | r2_hidden(sK1,sK3(sK0,sK1,sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u243,negated_conjecture,
% 1.33/0.55      r2_lattice3(sK0,X4,sK2(sK0,k1_tarski(sK1),sK1)) | r2_hidden(sK2(sK0,X4,sK2(sK0,k1_tarski(sK1),sK1)),X4) | m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.33/0.55  
% 1.33/0.55  cnf(u242,negated_conjecture,
% 1.33/0.55      r2_lattice3(sK0,X3,sK2(sK0,k1_tarski(sK1),sK1)) | m1_subset_1(sK2(sK0,X3,sK2(sK0,k1_tarski(sK1),sK1)),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.33/0.55  
% 1.33/0.55  cnf(u81,negated_conjecture,
% 1.33/0.55      r2_lattice3(sK0,X0,sK1) | r2_hidden(sK2(sK0,X0,sK1),X0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u86,negated_conjecture,
% 1.33/0.55      r2_lattice3(sK0,X0,sK1) | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0))).
% 1.33/0.55  
% 1.33/0.55  % (2516)Refutation not found, incomplete strategy% (2516)------------------------------
% 1.33/0.55  % (2516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (2516)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (2516)Memory used [KB]: 1791
% 1.33/0.55  % (2516)Time elapsed: 0.135 s
% 1.33/0.55  % (2516)------------------------------
% 1.33/0.55  % (2516)------------------------------
% 1.33/0.55  cnf(u49,axiom,
% 1.33/0.55      ~r2_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u225,negated_conjecture,
% 1.33/0.55      v6_orders_2(k6_domain_1(u1_struct_0(sK0),sK2(sK0,k1_tarski(sK1),sK1)),sK0) | r2_hidden(sK1,sK3(sK0,sK1,sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u237,negated_conjecture,
% 1.33/0.55      v6_orders_2(k6_domain_1(u1_struct_0(sK0),sK2(sK0,k1_tarski(sK1),sK1)),sK0) | m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.33/0.55  
% 1.33/0.55  cnf(u163,negated_conjecture,
% 1.33/0.55      v6_orders_2(sK3(sK0,sK1,sK1),sK0) | r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),k1_tarski(sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u198,negated_conjecture,
% 1.33/0.55      v6_orders_2(sK3(sK0,sK1,sK1),sK0) | m1_subset_1(sK2(sK0,k1_tarski(sK1),sK1),u1_struct_0(sK0))).
% 1.33/0.55  
% 1.33/0.55  cnf(u373,negated_conjecture,
% 1.33/0.55      v6_orders_2(sK3(sK0,sK1,sK1),sK0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u115,negated_conjecture,
% 1.33/0.55      v6_orders_2(k1_tarski(sK1),sK0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u57,axiom,
% 1.33/0.55      ~v6_orders_2(X4,X0) | r1_orders_2(X0,X1,X2) | ~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u42,negated_conjecture,
% 1.33/0.55      v3_orders_2(sK0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u65,axiom,
% 1.33/0.55      ~v3_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(X2,sK3(X0,X1,X2))).
% 1.33/0.55  
% 1.33/0.55  cnf(u64,axiom,
% 1.33/0.55      ~v3_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(X2,sK3(X0,X1,X2))).
% 1.33/0.55  
% 1.33/0.55  cnf(u63,axiom,
% 1.33/0.55      ~v3_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(X1,sK3(X0,X1,X2))).
% 1.33/0.55  
% 1.33/0.55  cnf(u62,axiom,
% 1.33/0.55      ~v3_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(X1,sK3(X0,X1,X2))).
% 1.33/0.55  
% 1.33/0.55  % (2507)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.33/0.55  cnf(u61,axiom,
% 1.33/0.55      ~v3_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))).
% 1.33/0.55  
% 1.33/0.55  cnf(u60,axiom,
% 1.33/0.55      ~v3_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))).
% 1.33/0.55  
% 1.33/0.55  cnf(u59,axiom,
% 1.33/0.55      ~v3_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v6_orders_2(sK3(X0,X1,X2),X0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u58,axiom,
% 1.33/0.55      ~v3_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v6_orders_2(sK3(X0,X1,X2),X0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u55,axiom,
% 1.33/0.55      ~v3_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u54,axiom,
% 1.33/0.55      ~v3_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) | v2_struct_0(X0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u250,negated_conjecture,
% 1.33/0.55      r1_orders_2(sK0,sK2(sK0,k1_tarski(sK1),sK1),sK1) | r1_orders_2(sK0,sK1,sK2(sK0,k1_tarski(sK1),sK1)) | r2_hidden(sK1,sK3(sK0,sK1,sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u249,negated_conjecture,
% 1.33/0.55      r1_orders_2(sK0,sK2(sK0,k1_tarski(sK1),sK1),sK1) | r1_orders_2(sK0,sK1,sK2(sK0,k1_tarski(sK1),sK1)) | m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.33/0.55  
% 1.33/0.55  cnf(u144,negated_conjecture,
% 1.33/0.55      r1_orders_2(sK0,sK1,sK1) | r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),k1_tarski(sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u166,negated_conjecture,
% 1.33/0.55      r1_orders_2(sK0,sK1,sK1) | m1_subset_1(sK2(sK0,k1_tarski(sK1),sK1),u1_struct_0(sK0))).
% 1.33/0.55  
% 1.33/0.55  cnf(u248,negated_conjecture,
% 1.33/0.55      r1_orders_2(sK0,sK1,sK1)).
% 1.33/0.55  
% 1.33/0.55  cnf(u110,negated_conjecture,
% 1.33/0.55      ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,X1,X0),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.33/0.55  
% 1.33/0.55  cnf(u108,negated_conjecture,
% 1.33/0.55      ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.33/0.55  
% 1.33/0.55  cnf(u106,negated_conjecture,
% 1.33/0.55      ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X0,sK3(sK0,X1,X0))).
% 1.33/0.55  
% 1.33/0.55  cnf(u104,negated_conjecture,
% 1.33/0.55      ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X1,sK3(sK0,X0,X1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u102,negated_conjecture,
% 1.33/0.55      ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,sK3(sK0,X1,X0))).
% 1.33/0.55  
% 1.33/0.55  cnf(u100,negated_conjecture,
% 1.33/0.55      ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK3(sK0,X0,X1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u98,negated_conjecture,
% 1.33/0.55      ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v6_orders_2(sK3(sK0,X1,X0),sK0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u96,negated_conjecture,
% 1.33/0.55      ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v6_orders_2(sK3(sK0,X0,X1),sK0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u56,axiom,
% 1.33/0.55      ~r1_orders_2(X0,X2,X1) | X1 = X2 | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u52,axiom,
% 1.33/0.55      ~r1_orders_2(X0,sK2(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u43,negated_conjecture,
% 1.33/0.55      v5_orders_2(sK0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u165,negated_conjecture,
% 1.33/0.55      m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),k1_tarski(sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u240,negated_conjecture,
% 1.33/0.55      m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k1_tarski(sK2(sK0,k1_tarski(sK1),sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK0,k1_tarski(sK1),sK1)) | v1_xboole_0(u1_struct_0(sK0))).
% 1.33/0.55  
% 1.33/0.55  cnf(u375,negated_conjecture,
% 1.33/0.55      m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.33/0.55  
% 1.33/0.55  cnf(u199,negated_conjecture,
% 1.33/0.55      m1_subset_1(sK2(sK0,k1_tarski(sK1),sK1),u1_struct_0(sK0)) | r2_hidden(sK1,sK3(sK0,sK1,sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u200,negated_conjecture,
% 1.33/0.55      m1_subset_1(sK2(sK0,k1_tarski(sK1),sK1),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.33/0.55  
% 1.33/0.55  cnf(u45,negated_conjecture,
% 1.33/0.55      m1_subset_1(sK1,u1_struct_0(sK0))).
% 1.33/0.55  
% 1.33/0.55  cnf(u224,negated_conjecture,
% 1.33/0.55      m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,k1_tarski(sK1),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,sK3(sK0,sK1,sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u236,negated_conjecture,
% 1.33/0.55      m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,k1_tarski(sK1),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.33/0.55  
% 1.33/0.55  cnf(u123,negated_conjecture,
% 1.33/0.55      m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.33/0.55  
% 1.33/0.55  cnf(u121,negated_conjecture,
% 1.33/0.55      ~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,k1_tarski(sK1)) | ~r2_hidden(X0,k1_tarski(sK1)) | r1_orders_2(sK0,X0,X1) | r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 1.33/0.55  
% 1.33/0.55  cnf(u503,negated_conjecture,
% 1.33/0.55      ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X0) | r1_orders_2(sK0,X0,sK1) | ~r2_hidden(X0,sK3(sK0,sK1,sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u445,negated_conjecture,
% 1.33/0.55      ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK3(sK0,sK1,sK1)) | r1_orders_2(sK0,sK1,X0) | m1_subset_1(sK2(sK0,k1_tarski(sK1),sK1),u1_struct_0(sK0)) | r1_orders_2(sK0,X0,sK1)).
% 1.33/0.55  
% 1.33/0.55  cnf(u441,negated_conjecture,
% 1.33/0.55      ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK3(sK0,sK1,sK1)) | r1_orders_2(sK0,sK1,X0) | r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),k1_tarski(sK1)) | r1_orders_2(sK0,X0,sK1)).
% 1.33/0.55  
% 1.33/0.55  cnf(u397,negated_conjecture,
% 1.33/0.55      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,sK3(sK0,sK1,sK1)) | ~r2_hidden(X0,sK3(sK0,sK1,sK1)) | r1_orders_2(sK0,X1,X0) | r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 1.33/0.55  
% 1.33/0.55  cnf(u241,negated_conjecture,
% 1.33/0.55      ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k1_tarski(sK1)) | r1_orders_2(sK0,X0,sK2(sK0,k1_tarski(sK1),sK1)) | r1_orders_2(sK0,sK2(sK0,k1_tarski(sK1),sK1),X0) | m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.33/0.55  
% 1.33/0.55  cnf(u229,negated_conjecture,
% 1.33/0.55      ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k1_tarski(sK1)) | r1_orders_2(sK0,X0,sK2(sK0,k1_tarski(sK1),sK1)) | r1_orders_2(sK0,sK2(sK0,k1_tarski(sK1),sK1),X0) | r2_hidden(sK1,sK3(sK0,sK1,sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u220,negated_conjecture,
% 1.33/0.55      ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X1) | ~r2_hidden(X1,sK3(sK0,sK1,sK1)) | ~r2_hidden(X0,sK3(sK0,sK1,sK1)) | r1_orders_2(sK0,X1,X0) | m1_subset_1(sK2(sK0,k1_tarski(sK1),sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 1.33/0.55  
% 1.33/0.55  cnf(u214,negated_conjecture,
% 1.33/0.55      ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X1) | ~r2_hidden(X1,sK3(sK0,sK1,sK1)) | ~r2_hidden(X0,sK3(sK0,sK1,sK1)) | r1_orders_2(sK0,X1,X0) | r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),k1_tarski(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 1.33/0.55  
% 1.33/0.55  cnf(u202,negated_conjecture,
% 1.33/0.55      ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,sK1) | r1_orders_2(sK0,sK1,X0) | ~r2_hidden(X0,k1_tarski(sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u167,negated_conjecture,
% 1.33/0.55      ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X1,k1_tarski(sK1)) | r1_orders_2(sK0,X1,X0) | r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,k1_tarski(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK0))).
% 1.33/0.55  
% 1.33/0.55  cnf(u118,negated_conjecture,
% 1.33/0.55      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0)) | r1_orders_2(sK0,X1,sK1)).
% 1.33/0.55  
% 1.33/0.55  cnf(u113,negated_conjecture,
% 1.33/0.55      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_hidden(sK2(sK0,X0,sK1),X0) | r1_orders_2(sK0,X1,sK1)).
% 1.33/0.55  
% 1.33/0.55  % (2519)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.33/0.55  cnf(u94,negated_conjecture,
% 1.33/0.55      ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.33/0.55  
% 1.33/0.55  cnf(u84,negated_conjecture,
% 1.33/0.55      ~m1_subset_1(X0,u1_struct_0(sK0)) | v6_orders_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u51,axiom,
% 1.33/0.55      ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK2(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u50,axiom,
% 1.33/0.55      ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u66,axiom,
% 1.33/0.55      ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u44,negated_conjecture,
% 1.33/0.55      l1_orders_2(sK0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u48,axiom,
% 1.33/0.55      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u228,negated_conjecture,
% 1.33/0.55      v1_xboole_0(u1_struct_0(sK0)) | k1_tarski(sK2(sK0,k1_tarski(sK1),sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK0,k1_tarski(sK1),sK1)) | r2_hidden(sK1,sK3(sK0,sK1,sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u124,negated_conjecture,
% 1.33/0.55      v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)) = k1_tarski(k1_tarski(sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u232,negated_conjecture,
% 1.33/0.55      v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK3(sK0,sK1,sK1)) = k1_tarski(sK3(sK0,sK1,sK1)) | r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),k1_tarski(sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u411,negated_conjecture,
% 1.33/0.55      v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK3(sK0,sK1,sK1)) = k1_tarski(sK3(sK0,sK1,sK1)) | k1_tarski(sK2(sK0,k1_tarski(sK1),sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK0,k1_tarski(sK1),sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u446,negated_conjecture,
% 1.33/0.55      v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK3(sK0,sK1,sK1)) = k1_tarski(sK3(sK0,sK1,sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u53,axiom,
% 1.33/0.55      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u74,negated_conjecture,
% 1.33/0.55      l1_struct_0(sK0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u41,negated_conjecture,
% 1.33/0.55      ~v2_struct_0(sK0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u69,axiom,
% 1.33/0.55      r2_hidden(sK4(X0,X1),X1) | sK4(X0,X1) = X0 | k1_tarski(X0) = X1).
% 1.33/0.55  
% 1.33/0.55  cnf(u164,negated_conjecture,
% 1.33/0.55      r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),k1_tarski(sK1)) | r2_hidden(sK1,sK3(sK0,sK1,sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u216,negated_conjecture,
% 1.33/0.55      r2_hidden(sK1,sK3(sK0,sK1,sK1)) | sK1 = sK2(sK0,k1_tarski(sK1),sK1)).
% 1.33/0.55  
% 1.33/0.55  cnf(u215,negated_conjecture,
% 1.33/0.55      r2_hidden(sK1,sK3(sK0,sK1,sK1)) | k1_tarski(sK1) = k1_tarski(sK2(sK0,k1_tarski(sK1),sK1)) | sK1 = sK4(sK2(sK0,k1_tarski(sK1),sK1),k1_tarski(sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u374,negated_conjecture,
% 1.33/0.55      r2_hidden(sK1,sK3(sK0,sK1,sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u253,negated_conjecture,
% 1.33/0.55      r2_hidden(sK1,sK3(sK0,sK1,sK1)) | sK4(X5,k1_tarski(sK1)) = X5 | k1_tarski(sK1) = k1_tarski(X5) | sK2(sK0,k1_tarski(sK1),sK1) = sK4(X5,k1_tarski(sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u257,negated_conjecture,
% 1.33/0.55      r2_hidden(sK1,sK3(sK0,sK1,sK1)) | sK4(sK2(sK0,k1_tarski(sK1),sK1),k1_tarski(sK1)) = sK4(X5,k1_tarski(sK1)) | sK4(X5,k1_tarski(sK1)) = X5 | k1_tarski(sK1) = k1_tarski(X5) | k1_tarski(sK1) = k1_tarski(sK2(sK0,k1_tarski(sK1),sK1))).
% 1.33/0.55  
% 1.33/0.55  cnf(u72,axiom,
% 1.33/0.55      r2_hidden(X3,k1_tarski(X3))).
% 1.33/0.55  
% 1.33/0.55  cnf(u354,axiom,
% 1.33/0.55      ~r2_hidden(sK4(X14,k1_tarski(X13)),k1_tarski(X13)) | sK4(X14,k1_tarski(X13)) != X12 | k1_tarski(X12) = k1_tarski(X13) | sK4(X12,k1_tarski(X13)) = X12 | k1_tarski(X13) = k1_tarski(X14)).
% 1.33/0.55  
% 1.33/0.55  cnf(u70,axiom,
% 1.33/0.55      ~r2_hidden(sK4(X0,X1),X1) | sK4(X0,X1) != X0 | k1_tarski(X0) = X1).
% 1.33/0.55  
% 1.33/0.55  cnf(u223,negated_conjecture,
% 1.33/0.55      ~r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),X2) | r2_hidden(sK1,sK3(sK0,sK1,sK1)) | r2_hidden(sK2(sK0,X2,sK1),X2) | r1_orders_2(sK0,sK2(sK0,k1_tarski(sK1),sK1),sK1)).
% 1.33/0.55  
% 1.33/0.55  cnf(u222,negated_conjecture,
% 1.33/0.55      ~r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),X1) | r2_hidden(sK1,sK3(sK0,sK1,sK1)) | m1_subset_1(sK2(sK0,X1,sK1),u1_struct_0(sK0)) | r1_orders_2(sK0,sK2(sK0,k1_tarski(sK1),sK1),sK1)).
% 1.33/0.55  
% 1.33/0.55  cnf(u235,negated_conjecture,
% 1.33/0.55      ~r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),X2) | m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2(sK0,X2,sK1),X2) | r1_orders_2(sK0,sK2(sK0,k1_tarski(sK1),sK1),sK1)).
% 1.33/0.55  
% 1.33/0.55  cnf(u234,negated_conjecture,
% 1.33/0.55      ~r2_hidden(sK2(sK0,k1_tarski(sK1),sK1),X1) | m1_subset_1(sK3(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,X1,sK1),u1_struct_0(sK0)) | r1_orders_2(sK0,sK2(sK0,k1_tarski(sK1),sK1),sK1)).
% 1.33/0.55  
% 1.33/0.55  cnf(u138,negated_conjecture,
% 1.33/0.55      ~r2_hidden(sK1,X0) | r2_hidden(sK2(sK0,X0,sK1),X0) | r1_orders_2(sK0,sK1,sK1)).
% 1.33/0.55  
% 1.33/0.55  cnf(u139,negated_conjecture,
% 1.33/0.55      ~r2_hidden(sK1,X0) | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK1)).
% 1.33/0.55  
% 1.33/0.55  cnf(u73,axiom,
% 1.33/0.55      ~r2_hidden(X3,k1_tarski(X0)) | X0 = X3).
% 1.33/0.55  
% 1.33/0.55  cnf(u136,axiom,
% 1.33/0.55      ~r2_hidden(X0,k1_tarski(X1)) | k1_tarski(X0) = k1_tarski(X1) | sK4(X0,k1_tarski(X1)) = X1).
% 1.33/0.55  
% 1.33/0.55  cnf(u206,axiom,
% 1.33/0.55      ~r2_hidden(X4,k1_tarski(X3)) | sK4(X2,k1_tarski(X3)) = X4 | sK4(X2,k1_tarski(X3)) = X2 | k1_tarski(X3) = k1_tarski(X2)).
% 1.33/0.55  
% 1.33/0.55  cnf(u209,axiom,
% 1.33/0.55      ~r2_hidden(X13,k1_tarski(X12)) | k1_tarski(X12) = k1_tarski(X13) | sK4(X11,k1_tarski(X12)) = sK4(X13,k1_tarski(X12)) | sK4(X11,k1_tarski(X12)) = X11 | k1_tarski(X12) = k1_tarski(X11)).
% 1.33/0.55  
% 1.33/0.55  cnf(u143,axiom,
% 1.33/0.55      sK4(sK4(X1,k1_tarski(X2)),k1_tarski(X2)) = X2 | k1_tarski(X2) = k1_tarski(sK4(X1,k1_tarski(X2))) | sK4(X1,k1_tarski(X2)) = X1 | k1_tarski(X1) = k1_tarski(X2)).
% 1.33/0.55  
% 1.33/0.55  cnf(u207,axiom,
% 1.33/0.55      sK4(X7,k1_tarski(X6)) = X7 | sK4(X5,k1_tarski(X6)) = sK4(X7,k1_tarski(X6)) | sK4(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 1.33/0.55  
% 1.33/0.55  cnf(u77,axiom,
% 1.33/0.55      sK4(X0,k1_tarski(X1)) = X0 | sK4(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 1.33/0.55  
% 1.33/0.55  cnf(u77,axiom,
% 1.33/0.55      sK4(X0,k1_tarski(X1)) = X0 | sK4(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 1.33/0.55  
% 1.33/0.55  cnf(u207,axiom,
% 1.33/0.55      sK4(X7,k1_tarski(X6)) = X7 | sK4(X5,k1_tarski(X6)) = sK4(X7,k1_tarski(X6)) | sK4(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 1.33/0.55  
% 1.33/0.55  cnf(u207,axiom,
% 1.33/0.55      sK4(X7,k1_tarski(X6)) = X7 | sK4(X5,k1_tarski(X6)) = sK4(X7,k1_tarski(X6)) | sK4(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 1.33/0.55  
% 1.33/0.55  cnf(u89,negated_conjecture,
% 1.33/0.55      k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)).
% 1.33/0.55  
% 1.33/0.55  cnf(u179,axiom,
% 1.33/0.55      k1_tarski(X5) = k1_tarski(sK4(X4,k1_tarski(X5))) | sK4(X4,k1_tarski(X5)) = X4 | k1_tarski(X5) = k1_tarski(X4)).
% 1.33/0.55  
% 1.33/0.55  cnf(u47,axiom,
% 1.33/0.55      k1_tarski(X0) = k2_tarski(X0,X0)).
% 1.33/0.55  
% 1.33/0.55  cnf(u312,axiom,
% 1.33/0.55      sK4(X2,k1_tarski(X1)) != X0 | sK4(X2,k1_tarski(X1)) = X2 | sK4(X0,k1_tarski(X1)) = X0 | k1_tarski(X1) = k1_tarski(X2) | k1_tarski(X0) = k1_tarski(X1)).
% 1.33/0.55  
% 1.33/0.55  cnf(u310,axiom,
% 1.33/0.55      sK4(X2,k1_tarski(X1)) != X0 | sK4(X0,k1_tarski(X1)) = sK4(X2,k1_tarski(X1)) | sK4(X2,k1_tarski(X1)) = X2 | k1_tarski(X0) = k1_tarski(X1) | k1_tarski(X1) = k1_tarski(X2)).
% 1.33/0.55  
% 1.33/0.55  cnf(u131,axiom,
% 1.33/0.55      X0 != X1 | sK4(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 1.33/0.55  
% 1.33/0.55  cnf(u137,axiom,
% 1.33/0.55      X0 != X1 | k1_tarski(X0) = k1_tarski(X1) | sK4(X0,k1_tarski(X1)) = X0).
% 1.33/0.55  
% 1.33/0.55  cnf(u91,negated_conjecture,
% 1.33/0.55      sK1 != k2_yellow_0(sK0,k1_tarski(sK1)) | sK1 != k1_yellow_0(sK0,k1_tarski(sK1))).
% 1.33/0.55  
% 1.33/0.55  % (2505)# SZS output end Saturation.
% 1.33/0.55  % (2505)------------------------------
% 1.33/0.55  % (2505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (2505)Termination reason: Satisfiable
% 1.33/0.55  
% 1.33/0.55  % (2505)Memory used [KB]: 1918
% 1.33/0.55  % (2505)Time elapsed: 0.117 s
% 1.33/0.55  % (2505)------------------------------
% 1.33/0.55  % (2505)------------------------------
% 1.33/0.55  % (2525)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.52/0.55  % (2497)Success in time 0.186 s
%------------------------------------------------------------------------------
