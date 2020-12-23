%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:22 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   26 (  26 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    0
%              Number of atoms          :   41 (  41 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u33,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) )).

cnf(u37,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | l1_pre_topc(X1)
    | ~ l1_pre_topc(X0) )).

cnf(u38,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) )).

cnf(u52,negated_conjecture,
    ( l1_pre_topc(sK1) )).

cnf(u32,negated_conjecture,
    ( l1_pre_topc(sK0) )).

cnf(u59,negated_conjecture,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u64,axiom,
    ( m1_subset_1(X1,k1_tarski(X1)) )).

cnf(u53,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u34,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) )).

cnf(u57,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u47,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u35,negated_conjecture,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u62,axiom,
    ( r2_hidden(X0,k1_tarski(X0)) )).

cnf(u41,axiom,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) )).

cnf(u42,axiom,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) )).

cnf(u60,negated_conjecture,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) )).

cnf(u49,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u65,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | u1_struct_0(sK0) = u1_struct_0(sK1) )).

cnf(u43,axiom,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
    | r2_hidden(X0,X1) )).

cnf(u48,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u40,axiom,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 )).

cnf(u46,axiom,
    ( ~ r1_tarski(X1,X0)
    | X0 = X1
    | ~ r1_tarski(X0,X1) )).

cnf(u66,negated_conjecture,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK0)) )).

cnf(u39,axiom,
    ( k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) )).

cnf(u36,axiom,
    ( k2_tarski(X0,X0) = k1_tarski(X0) )).

cnf(u54,axiom,
    ( k2_xboole_0(X0,X0) = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:26:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (25445)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (25462)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (25462)Refutation not found, incomplete strategy% (25462)------------------------------
% 0.20/0.50  % (25462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (25462)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (25462)Memory used [KB]: 1663
% 0.20/0.50  % (25462)Time elapsed: 0.002 s
% 0.20/0.50  % (25462)------------------------------
% 0.20/0.50  % (25462)------------------------------
% 0.20/0.50  % (25438)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.51  % (25438)# SZS output start Saturation.
% 0.20/0.51  cnf(u33,negated_conjecture,
% 0.20/0.51      m1_pre_topc(sK1,sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u37,axiom,
% 0.20/0.51      ~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u38,axiom,
% 0.20/0.51      ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u52,negated_conjecture,
% 0.20/0.51      l1_pre_topc(sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u32,negated_conjecture,
% 0.20/0.51      l1_pre_topc(sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u59,negated_conjecture,
% 0.20/0.51      m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u64,axiom,
% 0.20/0.51      m1_subset_1(X1,k1_tarski(X1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u53,axiom,
% 0.20/0.51      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u34,negated_conjecture,
% 0.20/0.51      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u57,negated_conjecture,
% 0.20/0.51      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u47,axiom,
% 0.20/0.51      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u35,negated_conjecture,
% 0.20/0.51      ~m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u62,axiom,
% 0.20/0.51      r2_hidden(X0,k1_tarski(X0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u41,axiom,
% 0.20/0.51      ~r2_hidden(X0,X1) | m1_subset_1(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u42,axiom,
% 0.20/0.51      ~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u60,negated_conjecture,
% 0.20/0.51      r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u49,axiom,
% 0.20/0.51      r1_tarski(X1,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u65,negated_conjecture,
% 0.20/0.51      ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | u1_struct_0(sK0) = u1_struct_0(sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u43,axiom,
% 0.20/0.51      ~r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) | r2_hidden(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u48,axiom,
% 0.20/0.51      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u40,axiom,
% 0.20/0.51      ~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1).
% 0.20/0.51  
% 0.20/0.51  cnf(u46,axiom,
% 0.20/0.51      ~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u66,negated_conjecture,
% 0.20/0.51      u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u39,axiom,
% 0.20/0.51      k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u36,axiom,
% 0.20/0.51      k2_tarski(X0,X0) = k1_tarski(X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u54,axiom,
% 0.20/0.51      k2_xboole_0(X0,X0) = X0).
% 0.20/0.51  
% 0.20/0.51  % (25438)# SZS output end Saturation.
% 0.20/0.51  % (25438)------------------------------
% 0.20/0.51  % (25438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (25438)Termination reason: Satisfiable
% 0.20/0.51  
% 0.20/0.51  % (25438)Memory used [KB]: 1663
% 0.20/0.51  % (25438)Time elapsed: 0.005 s
% 0.20/0.51  % (25438)------------------------------
% 0.20/0.51  % (25438)------------------------------
% 0.20/0.51  % (25426)Success in time 0.157 s
%------------------------------------------------------------------------------
