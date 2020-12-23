%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:22 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   28 (  28 expanded)
%              Number of leaves         :   28 (  28 expanded)
%              Depth                    :    0
%              Number of atoms          :   58 (  58 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u28,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u26,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u29,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) )).

cnf(u56,negated_conjecture,
    ( ~ m1_pre_topc(sK0,X0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) )).

cnf(u53,axiom,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) )).

cnf(u46,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK1)
    | l1_pre_topc(X0) )).

cnf(u44,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | l1_pre_topc(X0) )).

cnf(u32,axiom,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) )).

cnf(u45,negated_conjecture,
    ( l1_pre_topc(sK1) )).

cnf(u27,negated_conjecture,
    ( l1_pre_topc(sK0) )).

cnf(u33,axiom,
    ( ~ l1_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | l1_pre_topc(X1) )).

cnf(u35,axiom,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X0,X1) )).

cnf(u57,negated_conjecture,
    ( ~ r2_hidden(X1,u1_struct_0(sK1))
    | m1_subset_1(X1,u1_struct_0(sK0)) )).

cnf(u49,axiom,
    ( ~ r2_hidden(X0,X2)
    | m1_subset_1(X0,X1)
    | ~ r1_tarski(X2,X1) )).

cnf(u64,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(sK1)) )).

cnf(u55,negated_conjecture,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u40,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) )).

cnf(u30,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) )).

cnf(u39,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2)
    | ~ r2_hidden(X0,X1) )).

cnf(u31,negated_conjecture,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u58,negated_conjecture,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) )).

cnf(u42,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u61,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | u1_struct_0(sK0) = u1_struct_0(sK1) )).

cnf(u52,axiom,
    ( ~ r1_tarski(X0,u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) )).

cnf(u38,axiom,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 )).

cnf(u50,axiom,
    ( ~ r1_tarski(X2,X1)
    | m1_subset_1(X0,X1)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X0,X2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:44:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (9634)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.46  % (9626)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (9626)Refutation not found, incomplete strategy% (9626)------------------------------
% 0.20/0.46  % (9626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (9634)# SZS output start Saturation.
% 0.20/0.46  cnf(u28,negated_conjecture,
% 0.20/0.46      ~v2_struct_0(sK1)).
% 0.20/0.46  
% 0.20/0.46  cnf(u26,negated_conjecture,
% 0.20/0.46      ~v2_struct_0(sK0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u29,negated_conjecture,
% 0.20/0.46      m1_pre_topc(sK1,sK0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u56,negated_conjecture,
% 0.20/0.46      ~m1_pre_topc(sK0,X0) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u53,axiom,
% 0.20/0.46      ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))).
% 0.20/0.46  
% 0.20/0.46  cnf(u46,negated_conjecture,
% 0.20/0.46      ~m1_pre_topc(X0,sK1) | l1_pre_topc(X0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u44,negated_conjecture,
% 0.20/0.46      ~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u32,axiom,
% 0.20/0.46      l1_struct_0(X0) | ~l1_pre_topc(X0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u45,negated_conjecture,
% 0.20/0.46      l1_pre_topc(sK1)).
% 0.20/0.46  
% 0.20/0.46  cnf(u27,negated_conjecture,
% 0.20/0.46      l1_pre_topc(sK0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u33,axiom,
% 0.20/0.46      ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)).
% 0.20/0.46  
% 0.20/0.46  cnf(u35,axiom,
% 0.20/0.46      r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)).
% 0.20/0.46  
% 0.20/0.46  cnf(u57,negated_conjecture,
% 0.20/0.46      ~r2_hidden(X1,u1_struct_0(sK1)) | m1_subset_1(X1,u1_struct_0(sK0))).
% 0.20/0.46  
% 0.20/0.46  cnf(u49,axiom,
% 0.20/0.46      ~r2_hidden(X0,X2) | m1_subset_1(X0,X1) | ~r1_tarski(X2,X1)).
% 0.20/0.46  
% 0.20/0.46  cnf(u64,negated_conjecture,
% 0.20/0.46      v1_xboole_0(u1_struct_0(sK1))).
% 0.20/0.46  
% 0.20/0.46  cnf(u55,negated_conjecture,
% 0.20/0.46      m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.46  
% 0.20/0.46  cnf(u40,axiom,
% 0.20/0.46      m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)).
% 0.20/0.46  
% 0.20/0.46  cnf(u30,negated_conjecture,
% 0.20/0.46      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.20/0.46  
% 0.20/0.46  cnf(u34,axiom,
% 0.20/0.46      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u39,axiom,
% 0.20/0.46      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.20/0.46  
% 0.20/0.46  cnf(u41,axiom,
% 0.20/0.46      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)).
% 0.20/0.46  
% 0.20/0.46  cnf(u31,negated_conjecture,
% 0.20/0.46      ~m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.46  
% 0.20/0.46  cnf(u58,negated_conjecture,
% 0.20/0.46      r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))).
% 0.20/0.46  
% 0.20/0.46  cnf(u42,axiom,
% 0.20/0.46      r1_tarski(X1,X1)).
% 0.20/0.46  
% 0.20/0.46  cnf(u61,negated_conjecture,
% 0.20/0.46      ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | u1_struct_0(sK0) = u1_struct_0(sK1)).
% 0.20/0.46  
% 0.20/0.46  cnf(u52,axiom,
% 0.20/0.46      ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_pre_topc(X2,X1) | ~l1_pre_topc(X1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))).
% 0.20/0.46  
% 0.20/0.46  cnf(u38,axiom,
% 0.20/0.46      ~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1).
% 0.20/0.46  
% 0.20/0.46  cnf(u50,axiom,
% 0.20/0.46      ~r1_tarski(X2,X1) | m1_subset_1(X0,X1) | v1_xboole_0(X2) | ~m1_subset_1(X0,X2)).
% 0.20/0.46  
% 0.20/0.46  % (9634)# SZS output end Saturation.
% 0.20/0.46  % (9634)------------------------------
% 0.20/0.46  % (9634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (9634)Termination reason: Satisfiable
% 0.20/0.46  
% 0.20/0.46  % (9634)Memory used [KB]: 6140
% 0.20/0.46  % (9634)Time elapsed: 0.049 s
% 0.20/0.46  % (9634)------------------------------
% 0.20/0.46  % (9634)------------------------------
% 0.20/0.46  % (9611)Success in time 0.108 s
%------------------------------------------------------------------------------
