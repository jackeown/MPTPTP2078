%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:21 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   25 (  25 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    0
%              Number of atoms          :   40 (  40 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u32,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) )).

cnf(u36,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) )).

cnf(u37,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) )).

cnf(u49,negated_conjecture,
    ( l1_pre_topc(sK1) )).

cnf(u31,negated_conjecture,
    ( l1_pre_topc(sK0) )).

cnf(u64,axiom,
    ( m1_subset_1(X0,k1_tarski(X0)) )).

cnf(u63,axiom,
    ( m1_subset_1(X0,k2_tarski(X0,X1)) )).

cnf(u56,axiom,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(k2_tarski(X0,X1))) )).

cnf(u59,axiom,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(k1_tarski(X0))) )).

cnf(u33,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) )).

cnf(u55,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u45,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2)
    | ~ r2_hidden(X0,X1) )).

cnf(u34,negated_conjecture,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u57,axiom,
    ( r2_hidden(X0,k1_tarski(X0)) )).

cnf(u53,axiom,
    ( r2_hidden(X0,k2_tarski(X0,X1)) )).

cnf(u61,axiom,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | m1_subset_1(X0,k2_tarski(X1,X2)) )).

cnf(u60,axiom,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | m1_subset_1(X0,k1_tarski(X1)) )).

cnf(u40,axiom,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) )).

cnf(u46,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u51,axiom,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
    | r2_hidden(X0,X1) )).

cnf(u44,axiom,
    ( ~ r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
    | r2_hidden(X0,X2) )).

cnf(u43,axiom,
    ( ~ r1_tarski(X1,X0)
    | X0 = X1
    | ~ r1_tarski(X0,X1) )).

cnf(u39,axiom,
    ( k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) )).

cnf(u35,axiom,
    ( k2_tarski(X0,X0) = k1_tarski(X0) )).

cnf(u38,axiom,
    ( k2_xboole_0(X0,X0) = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (1156)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (1159)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.52  % (1159)# SZS output start Saturation.
% 0.20/0.52  cnf(u32,negated_conjecture,
% 0.20/0.52      m1_pre_topc(sK1,sK0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u36,axiom,
% 0.20/0.52      ~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u37,axiom,
% 0.20/0.52      ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u49,negated_conjecture,
% 0.20/0.52      l1_pre_topc(sK1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u31,negated_conjecture,
% 0.20/0.52      l1_pre_topc(sK0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u64,axiom,
% 0.20/0.52      m1_subset_1(X0,k1_tarski(X0))).
% 0.20/0.52  
% 0.20/0.52  cnf(u63,axiom,
% 0.20/0.52      m1_subset_1(X0,k2_tarski(X0,X1))).
% 0.20/0.52  
% 0.20/0.52  cnf(u56,axiom,
% 0.20/0.52      m1_subset_1(k1_tarski(X0),k1_zfmisc_1(k2_tarski(X0,X1)))).
% 0.20/0.52  
% 0.20/0.52  cnf(u59,axiom,
% 0.20/0.52      m1_subset_1(k1_tarski(X0),k1_zfmisc_1(k1_tarski(X0)))).
% 0.20/0.52  
% 0.20/0.52  cnf(u33,negated_conjecture,
% 0.20/0.52      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.20/0.52  
% 0.20/0.52  cnf(u55,negated_conjecture,
% 0.20/0.52      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.52  
% 0.20/0.52  cnf(u45,axiom,
% 0.20/0.52      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u34,negated_conjecture,
% 0.20/0.52      ~m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.52  
% 0.20/0.52  cnf(u57,axiom,
% 0.20/0.52      r2_hidden(X0,k1_tarski(X0))).
% 0.20/0.52  
% 0.20/0.52  cnf(u53,axiom,
% 0.20/0.52      r2_hidden(X0,k2_tarski(X0,X1))).
% 0.20/0.52  
% 0.20/0.52  cnf(u61,axiom,
% 0.20/0.52      ~r2_hidden(X0,k1_tarski(X1)) | m1_subset_1(X0,k2_tarski(X1,X2))).
% 0.20/0.52  
% 0.20/0.52  cnf(u60,axiom,
% 0.20/0.52      ~r2_hidden(X0,k1_tarski(X1)) | m1_subset_1(X0,k1_tarski(X1))).
% 0.20/0.52  
% 0.20/0.52  cnf(u40,axiom,
% 0.20/0.52      ~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))).
% 0.20/0.52  
% 0.20/0.52  cnf(u46,axiom,
% 0.20/0.52      r1_tarski(X1,X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u51,axiom,
% 0.20/0.52      ~r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) | r2_hidden(X0,X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u44,axiom,
% 0.20/0.52      ~r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) | r2_hidden(X0,X2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u43,axiom,
% 0.20/0.52      ~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u39,axiom,
% 0.20/0.52      k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u35,axiom,
% 0.20/0.52      k2_tarski(X0,X0) = k1_tarski(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u38,axiom,
% 0.20/0.52      k2_xboole_0(X0,X0) = X0).
% 0.20/0.52  
% 0.20/0.52  % (1159)# SZS output end Saturation.
% 0.20/0.52  % (1159)------------------------------
% 0.20/0.52  % (1159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (1159)Termination reason: Satisfiable
% 0.20/0.52  
% 0.20/0.52  % (1159)Memory used [KB]: 1663
% 0.20/0.52  % (1159)Time elapsed: 0.112 s
% 0.20/0.52  % (1159)------------------------------
% 0.20/0.52  % (1159)------------------------------
% 0.20/0.52  % (1150)Success in time 0.164 s
%------------------------------------------------------------------------------
