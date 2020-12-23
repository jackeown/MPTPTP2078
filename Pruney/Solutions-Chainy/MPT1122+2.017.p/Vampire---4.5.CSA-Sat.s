%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:20 EST 2020

% Result     : CounterSatisfiable 0.18s
% Output     : Saturation 0.18s
% Verified   : 
% Statistics : Number of clauses        :   37 (  37 expanded)
%              Number of leaves         :   37 (  37 expanded)
%              Depth                    :    0
%              Number of atoms          :   84 (  84 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u56,axiom,
    ( ~ v2_pre_topc(X0)
    | u1_struct_0(X0) != k2_pre_topc(X0,u1_struct_0(X0))
    | v4_pre_topc(u1_struct_0(X0),X0)
    | ~ l1_pre_topc(X0) )).

cnf(u57,axiom,
    ( ~ v2_pre_topc(X1)
    | k4_xboole_0(u1_struct_0(X1),X2) != k2_pre_topc(X1,k4_xboole_0(u1_struct_0(X1),X2))
    | v4_pre_topc(k4_xboole_0(u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1) )).

cnf(u58,negated_conjecture,
    ( ~ v2_pre_topc(sK0)
    | sK1 != k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0) )).

cnf(u45,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u64,axiom,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) )).

cnf(u65,axiom,
    ( ~ l1_struct_0(X1)
    | k4_xboole_0(u1_struct_0(X1),X2) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k4_xboole_0(u1_struct_0(X1),X2))) )).

cnf(u26,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | v2_pre_topc(sK0) )).

cnf(u28,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u39,axiom,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) )).

cnf(u31,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u53,axiom,
    ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(X1),X2),X1)
    | k4_xboole_0(u1_struct_0(X1),X2) = k2_pre_topc(X1,k4_xboole_0(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1) )).

cnf(u61,axiom,
    ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(X1),X2),X1)
    | v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k4_xboole_0(u1_struct_0(X1),X2)),X1)
    | ~ l1_pre_topc(X1) )).

cnf(u52,axiom,
    ( ~ v4_pre_topc(u1_struct_0(X0),X0)
    | u1_struct_0(X0) = k2_pre_topc(X0,u1_struct_0(X0))
    | ~ l1_pre_topc(X0) )).

cnf(u60,axiom,
    ( ~ v4_pre_topc(u1_struct_0(X0),X0)
    | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)),X0)
    | ~ l1_pre_topc(X0) )).

cnf(u54,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) )).

cnf(u62,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) )).

cnf(u24,negated_conjecture,
    ( l1_pre_topc(sK0) )).

cnf(u35,axiom,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) )).

cnf(u43,axiom,
    ( m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) )).

cnf(u44,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u25,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u74,negated_conjecture,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0)
    | ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) )).

cnf(u71,negated_conjecture,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0)
    | ~ v3_pre_topc(u1_struct_0(sK0),sK0) )).

cnf(u68,negated_conjecture,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ v3_pre_topc(sK1,sK0) )).

cnf(u36,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_pre_topc(X1,X0)
    | k2_pre_topc(X0,X1) = X1
    | ~ l1_pre_topc(X0) )).

cnf(u37,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k2_pre_topc(X0,X1) != X1
    | ~ v2_pre_topc(X0)
    | v4_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) )).

cnf(u38,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v4_pre_topc(X1,X0)
    | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | ~ l1_pre_topc(X0) )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
    | ~ l1_struct_0(X0) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u66,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u69,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u50,axiom,
    ( k7_subset_1(X3,k4_xboole_0(X3,X4),X5) = k4_xboole_0(k4_xboole_0(X3,X4),X5) )).

cnf(u48,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u72,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK0),X0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))) )).

cnf(u49,axiom,
    ( k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u32,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u27,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
    | v2_pre_topc(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n008.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 12:01:00 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.40  % (487)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.18/0.40  % (476)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.18/0.40  % SZS status CounterSatisfiable for theBenchmark
% 0.18/0.40  % (487)# SZS output start Saturation.
% 0.18/0.40  cnf(u56,axiom,
% 0.18/0.40      ~v2_pre_topc(X0) | u1_struct_0(X0) != k2_pre_topc(X0,u1_struct_0(X0)) | v4_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0)).
% 0.18/0.40  
% 0.18/0.40  cnf(u57,axiom,
% 0.18/0.40      ~v2_pre_topc(X1) | k4_xboole_0(u1_struct_0(X1),X2) != k2_pre_topc(X1,k4_xboole_0(u1_struct_0(X1),X2)) | v4_pre_topc(k4_xboole_0(u1_struct_0(X1),X2),X1) | ~l1_pre_topc(X1)).
% 0.18/0.40  
% 0.18/0.40  cnf(u58,negated_conjecture,
% 0.18/0.40      ~v2_pre_topc(sK0) | sK1 != k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0)).
% 0.18/0.40  
% 0.18/0.40  cnf(u45,negated_conjecture,
% 0.18/0.40      l1_struct_0(sK0)).
% 0.18/0.40  
% 0.18/0.40  cnf(u64,axiom,
% 0.18/0.40      ~l1_struct_0(X0) | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)))).
% 0.18/0.40  
% 0.18/0.40  cnf(u65,axiom,
% 0.18/0.40      ~l1_struct_0(X1) | k4_xboole_0(u1_struct_0(X1),X2) = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k4_xboole_0(u1_struct_0(X1),X2)))).
% 0.18/0.40  
% 0.18/0.40  cnf(u26,negated_conjecture,
% 0.18/0.40      v3_pre_topc(sK1,sK0) | v2_pre_topc(sK0)).
% 0.18/0.40  
% 0.18/0.40  cnf(u28,negated_conjecture,
% 0.18/0.40      v3_pre_topc(sK1,sK0) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.18/0.40  
% 0.18/0.40  cnf(u39,axiom,
% 0.18/0.40      ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)).
% 0.18/0.40  
% 0.18/0.40  cnf(u31,negated_conjecture,
% 0.18/0.40      ~v3_pre_topc(sK1,sK0) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.18/0.40  
% 0.18/0.40  cnf(u53,axiom,
% 0.18/0.40      ~v4_pre_topc(k4_xboole_0(u1_struct_0(X1),X2),X1) | k4_xboole_0(u1_struct_0(X1),X2) = k2_pre_topc(X1,k4_xboole_0(u1_struct_0(X1),X2)) | ~l1_pre_topc(X1)).
% 0.18/0.40  
% 0.18/0.40  cnf(u61,axiom,
% 0.18/0.40      ~v4_pre_topc(k4_xboole_0(u1_struct_0(X1),X2),X1) | v3_pre_topc(k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k4_xboole_0(u1_struct_0(X1),X2)),X1) | ~l1_pre_topc(X1)).
% 0.18/0.40  
% 0.18/0.40  cnf(u52,axiom,
% 0.18/0.40      ~v4_pre_topc(u1_struct_0(X0),X0) | u1_struct_0(X0) = k2_pre_topc(X0,u1_struct_0(X0)) | ~l1_pre_topc(X0)).
% 0.18/0.40  
% 0.18/0.40  cnf(u60,axiom,
% 0.18/0.40      ~v4_pre_topc(u1_struct_0(X0),X0) | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)),X0) | ~l1_pre_topc(X0)).
% 0.18/0.40  
% 0.18/0.41  cnf(u54,negated_conjecture,
% 0.18/0.41      ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)).
% 0.18/0.41  
% 0.18/0.41  cnf(u62,negated_conjecture,
% 0.18/0.41      ~v4_pre_topc(sK1,sK0) | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)).
% 0.18/0.41  
% 0.18/0.41  cnf(u24,negated_conjecture,
% 0.18/0.41      l1_pre_topc(sK0)).
% 0.18/0.41  
% 0.18/0.41  cnf(u35,axiom,
% 0.18/0.41      ~l1_pre_topc(X0) | l1_struct_0(X0)).
% 0.18/0.41  
% 0.18/0.41  cnf(u43,axiom,
% 0.18/0.41      m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))).
% 0.18/0.41  
% 0.18/0.41  cnf(u44,axiom,
% 0.18/0.41      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.18/0.41  
% 0.18/0.41  cnf(u25,negated_conjecture,
% 0.18/0.41      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.18/0.41  
% 0.18/0.41  cnf(u74,negated_conjecture,
% 0.18/0.41      ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0) | ~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0)).
% 0.18/0.41  
% 0.18/0.41  cnf(u71,negated_conjecture,
% 0.18/0.41      ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0) | ~v3_pre_topc(u1_struct_0(sK0),sK0)).
% 0.18/0.41  
% 0.18/0.41  cnf(u68,negated_conjecture,
% 0.18/0.41      ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) | ~v3_pre_topc(sK1,sK0)).
% 0.18/0.41  
% 0.18/0.41  cnf(u36,axiom,
% 0.18/0.41      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)).
% 0.18/0.41  
% 0.18/0.41  cnf(u37,axiom,
% 0.18/0.41      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0)).
% 0.18/0.41  
% 0.18/0.41  cnf(u38,axiom,
% 0.18/0.41      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~l1_pre_topc(X0)).
% 0.18/0.41  
% 0.18/0.41  cnf(u34,axiom,
% 0.18/0.41      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~l1_struct_0(X0)).
% 0.18/0.41  
% 0.18/0.41  cnf(u42,axiom,
% 0.18/0.41      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.18/0.41  
% 0.18/0.41  cnf(u66,negated_conjecture,
% 0.18/0.41      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.18/0.41  
% 0.18/0.41  cnf(u69,negated_conjecture,
% 0.18/0.41      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.18/0.41  
% 0.18/0.41  cnf(u50,axiom,
% 0.18/0.41      k7_subset_1(X3,k4_xboole_0(X3,X4),X5) = k4_xboole_0(k4_xboole_0(X3,X4),X5)).
% 0.18/0.41  
% 0.18/0.41  cnf(u48,negated_conjecture,
% 0.18/0.41      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 0.18/0.41  
% 0.18/0.41  cnf(u72,negated_conjecture,
% 0.18/0.41      k4_xboole_0(u1_struct_0(sK0),X0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)))).
% 0.18/0.41  
% 0.18/0.41  cnf(u49,axiom,
% 0.18/0.41      k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.18/0.41  
% 0.18/0.41  cnf(u32,axiom,
% 0.18/0.41      k2_subset_1(X0) = X0).
% 0.18/0.41  
% 0.18/0.41  cnf(u27,negated_conjecture,
% 0.18/0.41      k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) | v2_pre_topc(sK0)).
% 0.18/0.41  
% 0.18/0.41  % (487)# SZS output end Saturation.
% 0.18/0.41  % (487)------------------------------
% 0.18/0.41  % (487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.41  % (487)Termination reason: Satisfiable
% 0.18/0.41  
% 0.18/0.41  % (487)Memory used [KB]: 1663
% 0.18/0.41  % (487)Time elapsed: 0.036 s
% 0.18/0.41  % (487)------------------------------
% 0.18/0.41  % (487)------------------------------
% 0.18/0.41  % (470)Success in time 0.071 s
%------------------------------------------------------------------------------
