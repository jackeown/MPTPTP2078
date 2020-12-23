%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:54 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   46 (  46 expanded)
%              Number of leaves         :   46 (  46 expanded)
%              Depth                    :    0
%              Number of atoms          :  140 ( 140 expanded)
%              Number of equality atoms :   72 (  72 expanded)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u74,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1) )).

cnf(u48,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u67,negated_conjecture,
    ( r3_orders_2(sK0,sK1,sK1) )).

cnf(u47,axiom,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u36,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u53,axiom,
    ( ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r3_orders_2(X0,X1,X1)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u39,axiom,
    ( ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u35,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u34,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u89,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k6_domain_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )).

cnf(u90,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k6_domain_1(u1_struct_0(sK0),sK1)) = k1_tarski(k6_domain_1(u1_struct_0(sK0),sK1)) )).

cnf(u55,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) )).

cnf(u56,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u49,axiom,
    ( ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X0,X1) )).

cnf(u75,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u37,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u100,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k6_domain_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(X1,X0) )).

cnf(u101,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k6_domain_1(u1_struct_0(sK0),sK1)) = k1_tarski(k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ r2_hidden(X1,X0) )).

cnf(u57,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ r2_hidden(X1,X0) )).

cnf(u68,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(X1,X0) )).

% (8200)Refutation not found, incomplete strategy% (8200)------------------------------
% (8200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
cnf(u63,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r3_orders_2(sK0,X0,X0) )).

cnf(u66,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u40,axiom,
    ( ~ m1_subset_1(X1,X0)
    | k6_domain_1(X0,X1) = k1_tarski(X1)
    | v1_xboole_0(X0) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X1,X0)
    | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
    | v1_xboole_0(X0) )).

cnf(u44,axiom,
    ( r2_hidden(sK2(X0,X1),X1)
    | sK2(X0,X1) = X0
    | k1_tarski(X0) = X1 )).

cnf(u51,axiom,
    ( r2_hidden(X3,k1_tarski(X3)) )).

cnf(u227,axiom,
    ( ~ r2_hidden(sK2(X14,k1_tarski(X13)),k1_tarski(X13))
    | sK2(X14,k1_tarski(X13)) != X12
    | k1_tarski(X12) = k1_tarski(X13)
    | sK2(X12,k1_tarski(X13)) = X12
    | k1_tarski(X13) = k1_tarski(X14) )).

cnf(u45,axiom,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | sK2(X0,X1) != X0
    | k1_tarski(X0) = X1 )).

cnf(u91,negated_conjecture,
    ( ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK0),sK1))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) )).

cnf(u52,axiom,
    ( ~ r2_hidden(X3,k1_tarski(X0))
    | X0 = X3 )).

cnf(u87,axiom,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | k1_tarski(X0) = k1_tarski(X1)
    | sK2(X0,k1_tarski(X1)) = X1 )).

cnf(u121,axiom,
    ( ~ r2_hidden(X4,k1_tarski(X3))
    | sK2(X2,k1_tarski(X3)) = X4
    | sK2(X2,k1_tarski(X3)) = X2
    | k1_tarski(X3) = k1_tarski(X2) )).

cnf(u124,axiom,
    ( ~ r2_hidden(X13,k1_tarski(X12))
    | k1_tarski(X12) = k1_tarski(X13)
    | sK2(X11,k1_tarski(X12)) = sK2(X13,k1_tarski(X12))
    | sK2(X11,k1_tarski(X12)) = X11
    | k1_tarski(X12) = k1_tarski(X11) )).

cnf(u99,negated_conjecture,
    ( sK2(X0,k6_domain_1(u1_struct_0(sK0),sK1)) = X0
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),sK1) )).

cnf(u96,axiom,
    ( sK2(sK2(X1,k1_tarski(X2)),k1_tarski(X2)) = X2
    | k1_tarski(X2) = k1_tarski(sK2(X1,k1_tarski(X2)))
    | sK2(X1,k1_tarski(X2)) = X1
    | k1_tarski(X1) = k1_tarski(X2) )).

cnf(u122,axiom,
    ( sK2(X7,k1_tarski(X6)) = X7
    | sK2(X5,k1_tarski(X6)) = sK2(X7,k1_tarski(X6))
    | sK2(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u58,axiom,
    ( sK2(X0,k1_tarski(X1)) = X0
    | sK2(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u58_001,axiom,
    ( sK2(X0,k1_tarski(X1)) = X0
    | sK2(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u122_002,axiom,
    ( sK2(X7,k1_tarski(X6)) = X7
    | sK2(X5,k1_tarski(X6)) = sK2(X7,k1_tarski(X6))
    | sK2(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u122_003,axiom,
    ( sK2(X7,k1_tarski(X6)) = X7
    | sK2(X5,k1_tarski(X6)) = sK2(X7,k1_tarski(X6))
    | sK2(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u113,axiom,
    ( k1_tarski(X5) = k1_tarski(sK2(X4,k1_tarski(X5)))
    | sK2(X4,k1_tarski(X5)) = X4
    | k1_tarski(X5) = k1_tarski(X4) )).

cnf(u38,axiom,
    ( k1_tarski(X0) = k2_tarski(X0,X0) )).

cnf(u185,axiom,
    ( sK2(X2,k1_tarski(X1)) != X0
    | sK2(X2,k1_tarski(X1)) = X2
    | sK2(X0,k1_tarski(X1)) = X0
    | k1_tarski(X1) = k1_tarski(X2)
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u183,axiom,
    ( sK2(X2,k1_tarski(X1)) != X0
    | sK2(X0,k1_tarski(X1)) = sK2(X2,k1_tarski(X1))
    | sK2(X2,k1_tarski(X1)) = X2
    | k1_tarski(X0) = k1_tarski(X1)
    | k1_tarski(X1) = k1_tarski(X2) )).

cnf(u82,axiom,
    ( X0 != X1
    | sK2(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u88,axiom,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1)
    | sK2(X0,k1_tarski(X1)) = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:20:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (8184)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (8200)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (8184)# SZS output start Saturation.
% 0.21/0.52  cnf(u74,negated_conjecture,
% 0.21/0.52      r1_orders_2(sK0,sK1,sK1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u48,axiom,
% 0.21/0.52      ~r1_orders_2(X0,X1,X2) | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u67,negated_conjecture,
% 0.21/0.52      r3_orders_2(sK0,sK1,sK1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u47,axiom,
% 0.21/0.52      ~r3_orders_2(X0,X1,X2) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u36,negated_conjecture,
% 0.21/0.52      l1_orders_2(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u53,axiom,
% 0.21/0.52      ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X1) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u39,axiom,
% 0.21/0.52      ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u35,negated_conjecture,
% 0.21/0.52      v3_orders_2(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u34,negated_conjecture,
% 0.21/0.52      ~v2_struct_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u89,negated_conjecture,
% 0.21/0.52      v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k6_domain_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.52  
% 0.21/0.52  cnf(u90,negated_conjecture,
% 0.21/0.52      v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k6_domain_1(u1_struct_0(sK0),sK1)) = k1_tarski(k6_domain_1(u1_struct_0(sK0),sK1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u55,negated_conjecture,
% 0.21/0.52      v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u56,negated_conjecture,
% 0.21/0.52      v1_xboole_0(u1_struct_0(sK0)) | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u49,axiom,
% 0.21/0.52      ~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u75,negated_conjecture,
% 0.21/0.52      m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u37,negated_conjecture,
% 0.21/0.52      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u100,negated_conjecture,
% 0.21/0.52      ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k6_domain_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u101,negated_conjecture,
% 0.21/0.52      ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k6_domain_1(u1_struct_0(sK0),sK1)) = k1_tarski(k6_domain_1(u1_struct_0(sK0),sK1)) | ~r2_hidden(X1,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u57,negated_conjecture,
% 0.21/0.52      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) | ~r2_hidden(X1,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u68,negated_conjecture,
% 0.21/0.52      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,X0)).
% 0.21/0.52  
% 0.21/0.52  % (8200)Refutation not found, incomplete strategy% (8200)------------------------------
% 0.21/0.52  % (8200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  cnf(u63,negated_conjecture,
% 0.21/0.53      ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,X0,X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u66,negated_conjecture,
% 0.21/0.53      ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.53  
% 0.21/0.53  cnf(u40,axiom,
% 0.21/0.53      ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u41,axiom,
% 0.21/0.53      ~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | v1_xboole_0(X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u44,axiom,
% 0.21/0.53      r2_hidden(sK2(X0,X1),X1) | sK2(X0,X1) = X0 | k1_tarski(X0) = X1).
% 0.21/0.53  
% 0.21/0.53  cnf(u51,axiom,
% 0.21/0.53      r2_hidden(X3,k1_tarski(X3))).
% 0.21/0.53  
% 0.21/0.53  cnf(u227,axiom,
% 0.21/0.53      ~r2_hidden(sK2(X14,k1_tarski(X13)),k1_tarski(X13)) | sK2(X14,k1_tarski(X13)) != X12 | k1_tarski(X12) = k1_tarski(X13) | sK2(X12,k1_tarski(X13)) = X12 | k1_tarski(X13) = k1_tarski(X14)).
% 0.21/0.53  
% 0.21/0.53  cnf(u45,axiom,
% 0.21/0.53      ~r2_hidden(sK2(X0,X1),X1) | sK2(X0,X1) != X0 | k1_tarski(X0) = X1).
% 0.21/0.53  
% 0.21/0.53  cnf(u91,negated_conjecture,
% 0.21/0.53      ~r2_hidden(X0,k6_domain_1(u1_struct_0(sK0),sK1)) | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u52,axiom,
% 0.21/0.53      ~r2_hidden(X3,k1_tarski(X0)) | X0 = X3).
% 0.21/0.53  
% 0.21/0.53  cnf(u87,axiom,
% 0.21/0.53      ~r2_hidden(X0,k1_tarski(X1)) | k1_tarski(X0) = k1_tarski(X1) | sK2(X0,k1_tarski(X1)) = X1).
% 0.21/0.53  
% 0.21/0.53  cnf(u121,axiom,
% 0.21/0.53      ~r2_hidden(X4,k1_tarski(X3)) | sK2(X2,k1_tarski(X3)) = X4 | sK2(X2,k1_tarski(X3)) = X2 | k1_tarski(X3) = k1_tarski(X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u124,axiom,
% 0.21/0.53      ~r2_hidden(X13,k1_tarski(X12)) | k1_tarski(X12) = k1_tarski(X13) | sK2(X11,k1_tarski(X12)) = sK2(X13,k1_tarski(X12)) | sK2(X11,k1_tarski(X12)) = X11 | k1_tarski(X12) = k1_tarski(X11)).
% 0.21/0.53  
% 0.21/0.53  cnf(u99,negated_conjecture,
% 0.21/0.53      sK2(X0,k6_domain_1(u1_struct_0(sK0),sK1)) = X0 | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) | k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),sK1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u96,axiom,
% 0.21/0.53      sK2(sK2(X1,k1_tarski(X2)),k1_tarski(X2)) = X2 | k1_tarski(X2) = k1_tarski(sK2(X1,k1_tarski(X2))) | sK2(X1,k1_tarski(X2)) = X1 | k1_tarski(X1) = k1_tarski(X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u122,axiom,
% 0.21/0.53      sK2(X7,k1_tarski(X6)) = X7 | sK2(X5,k1_tarski(X6)) = sK2(X7,k1_tarski(X6)) | sK2(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 0.21/0.53  
% 0.21/0.53  cnf(u58,axiom,
% 0.21/0.53      sK2(X0,k1_tarski(X1)) = X0 | sK2(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u58,axiom,
% 0.21/0.53      sK2(X0,k1_tarski(X1)) = X0 | sK2(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u122,axiom,
% 0.21/0.53      sK2(X7,k1_tarski(X6)) = X7 | sK2(X5,k1_tarski(X6)) = sK2(X7,k1_tarski(X6)) | sK2(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 0.21/0.53  
% 0.21/0.53  cnf(u122,axiom,
% 0.21/0.53      sK2(X7,k1_tarski(X6)) = X7 | sK2(X5,k1_tarski(X6)) = sK2(X7,k1_tarski(X6)) | sK2(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 0.21/0.53  
% 0.21/0.53  cnf(u113,axiom,
% 0.21/0.53      k1_tarski(X5) = k1_tarski(sK2(X4,k1_tarski(X5))) | sK2(X4,k1_tarski(X5)) = X4 | k1_tarski(X5) = k1_tarski(X4)).
% 0.21/0.53  
% 0.21/0.53  cnf(u38,axiom,
% 0.21/0.53      k1_tarski(X0) = k2_tarski(X0,X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u185,axiom,
% 0.21/0.53      sK2(X2,k1_tarski(X1)) != X0 | sK2(X2,k1_tarski(X1)) = X2 | sK2(X0,k1_tarski(X1)) = X0 | k1_tarski(X1) = k1_tarski(X2) | k1_tarski(X0) = k1_tarski(X1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u183,axiom,
% 0.21/0.53      sK2(X2,k1_tarski(X1)) != X0 | sK2(X0,k1_tarski(X1)) = sK2(X2,k1_tarski(X1)) | sK2(X2,k1_tarski(X1)) = X2 | k1_tarski(X0) = k1_tarski(X1) | k1_tarski(X1) = k1_tarski(X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u82,axiom,
% 0.21/0.53      X0 != X1 | sK2(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u88,axiom,
% 0.21/0.53      X0 != X1 | k1_tarski(X0) = k1_tarski(X1) | sK2(X0,k1_tarski(X1)) = X0).
% 0.21/0.53  
% 0.21/0.53  % (8184)# SZS output end Saturation.
% 0.21/0.53  % (8184)------------------------------
% 0.21/0.53  % (8184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8184)Termination reason: Satisfiable
% 0.21/0.53  
% 0.21/0.53  % (8184)Memory used [KB]: 1791
% 0.21/0.53  % (8184)Time elapsed: 0.092 s
% 0.21/0.53  % (8184)------------------------------
% 0.21/0.53  % (8184)------------------------------
% 0.21/0.53  % (8179)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (8176)Success in time 0.167 s
%------------------------------------------------------------------------------
