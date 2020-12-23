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
% DateTime   : Thu Dec  3 13:09:21 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   46 (  46 expanded)
%              Number of leaves         :   46 (  46 expanded)
%              Depth                    :    0
%              Number of atoms          :  103 ( 103 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u29,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u27,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u30,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) )).

cnf(u63,negated_conjecture,
    ( ~ m1_pre_topc(sK0,X0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) )).

cnf(u60,axiom,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) )).

cnf(u51,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK1)
    | l1_pre_topc(X0) )).

cnf(u49,negated_conjecture,
    ( ~ m1_pre_topc(X0,sK0)
    | l1_pre_topc(X0) )).

cnf(u33,axiom,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) )).

cnf(u50,negated_conjecture,
    ( l1_pre_topc(sK1) )).

cnf(u28,negated_conjecture,
    ( l1_pre_topc(sK0) )).

cnf(u34,axiom,
    ( ~ l1_pre_topc(X0)
    | ~ m1_pre_topc(X1,X0)
    | l1_pre_topc(X1) )).

cnf(u70,negated_conjecture,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1)) )).

cnf(u36,axiom,
    ( r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0) )).

cnf(u110,negated_conjecture,
    ( ~ r2_hidden(X0,sK2) )).

cnf(u64,negated_conjecture,
    ( ~ r2_hidden(X1,u1_struct_0(sK1))
    | r2_hidden(X1,u1_struct_0(sK0)) )).

cnf(u113,negated_conjecture,
    ( ~ r2_hidden(X0,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u37,axiom,
    ( ~ r2_hidden(X1,X0)
    | m1_subset_1(X1,X0)
    | v1_xboole_0(X0) )).

cnf(u56,axiom,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) )).

cnf(u62,negated_conjecture,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u106,negated_conjecture,
    ( m1_subset_1(X2,sK2)
    | ~ v1_xboole_0(X2) )).

cnf(u75,negated_conjecture,
    ( m1_subset_1(X2,u1_struct_0(sK1))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u45,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) )).

cnf(u31,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) )).

cnf(u107,negated_conjecture,
    ( ~ m1_subset_1(X3,sK2)
    | v1_xboole_0(X3) )).

cnf(u67,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1)) )).

cnf(u76,negated_conjecture,
    ( ~ m1_subset_1(X3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(X3) )).

cnf(u105,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | ~ r2_hidden(X1,X0) )).

cnf(u74,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ r2_hidden(X1,X0) )).

cnf(u35,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) )).

cnf(u44,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u40,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ r2_hidden(X2,X1)
    | r2_hidden(X2,X0) )).

cnf(u32,negated_conjecture,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u104,negated_conjecture,
    ( v1_xboole_0(sK2) )).

cnf(u73,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u38,axiom,
    ( ~ v1_xboole_0(X0)
    | ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X1) )).

cnf(u39,axiom,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | m1_subset_1(X1,X0) )).

cnf(u46,axiom,
    ( ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X0,X1) )).

cnf(u65,negated_conjecture,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) )).

cnf(u47,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u71,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),X0)
    | r2_hidden(sK2,X0)
    | v1_xboole_0(u1_struct_0(sK1)) )).

cnf(u68,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | u1_struct_0(sK0) = u1_struct_0(sK1) )).

cnf(u109,negated_conjecture,
    ( ~ r1_tarski(X1,sK2)
    | ~ r2_hidden(X0,X1) )).

cnf(u112,negated_conjecture,
    ( ~ r1_tarski(X1,u1_struct_0(sK1))
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u59,axiom,
    ( ~ r1_tarski(X0,u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) )).

cnf(u43,axiom,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 )).

cnf(u57,axiom,
    ( ~ r1_tarski(X2,X1)
    | r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X2)
    | v1_xboole_0(X2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:46:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (24157)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (24152)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (24173)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (24157)Refutation not found, incomplete strategy% (24157)------------------------------
% 0.20/0.50  % (24157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (24157)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (24157)Memory used [KB]: 10490
% 0.20/0.50  % (24157)Time elapsed: 0.082 s
% 0.20/0.50  % (24157)------------------------------
% 0.20/0.50  % (24157)------------------------------
% 0.20/0.50  % (24152)Refutation not found, incomplete strategy% (24152)------------------------------
% 0.20/0.50  % (24152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (24166)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.50  % (24152)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (24152)Memory used [KB]: 10618
% 0.20/0.50  % (24152)Time elapsed: 0.088 s
% 0.20/0.50  % (24152)------------------------------
% 0.20/0.50  % (24152)------------------------------
% 0.20/0.50  % (24155)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (24168)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  % (24172)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.51  % (24172)# SZS output start Saturation.
% 0.20/0.51  cnf(u29,negated_conjecture,
% 0.20/0.51      ~v2_struct_0(sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u27,negated_conjecture,
% 0.20/0.51      ~v2_struct_0(sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u30,negated_conjecture,
% 0.20/0.51      m1_pre_topc(sK1,sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u63,negated_conjecture,
% 0.20/0.51      ~m1_pre_topc(sK0,X0) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u60,axiom,
% 0.20/0.51      ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u51,negated_conjecture,
% 0.20/0.51      ~m1_pre_topc(X0,sK1) | l1_pre_topc(X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u49,negated_conjecture,
% 0.20/0.51      ~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u33,axiom,
% 0.20/0.51      l1_struct_0(X0) | ~l1_pre_topc(X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u50,negated_conjecture,
% 0.20/0.51      l1_pre_topc(sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u28,negated_conjecture,
% 0.20/0.51      l1_pre_topc(sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u34,axiom,
% 0.20/0.51      ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u70,negated_conjecture,
% 0.20/0.51      r2_hidden(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u36,axiom,
% 0.20/0.51      r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u110,negated_conjecture,
% 0.20/0.51      ~r2_hidden(X0,sK2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u64,negated_conjecture,
% 0.20/0.51      ~r2_hidden(X1,u1_struct_0(sK1)) | r2_hidden(X1,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u113,negated_conjecture,
% 0.20/0.51      ~r2_hidden(X0,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u37,axiom,
% 0.20/0.51      ~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u56,axiom,
% 0.20/0.51      ~r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~r1_tarski(X1,X2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u62,negated_conjecture,
% 0.20/0.51      m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u106,negated_conjecture,
% 0.20/0.51      m1_subset_1(X2,sK2) | ~v1_xboole_0(X2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u75,negated_conjecture,
% 0.20/0.51      m1_subset_1(X2,u1_struct_0(sK1)) | ~v1_xboole_0(X2) | v1_xboole_0(u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u45,axiom,
% 0.20/0.51      m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u31,negated_conjecture,
% 0.20/0.51      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u107,negated_conjecture,
% 0.20/0.51      ~m1_subset_1(X3,sK2) | v1_xboole_0(X3)).
% 0.20/0.51  
% 0.20/0.51  cnf(u67,negated_conjecture,
% 0.20/0.51      ~m1_subset_1(X1,u1_struct_0(sK1)) | r2_hidden(X1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u76,negated_conjecture,
% 0.20/0.51      ~m1_subset_1(X3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(X3)).
% 0.20/0.51  
% 0.20/0.51  cnf(u105,negated_conjecture,
% 0.20/0.51      ~m1_subset_1(X0,k1_zfmisc_1(sK2)) | ~r2_hidden(X1,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u74,negated_conjecture,
% 0.20/0.51      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK0)) | ~r2_hidden(X1,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u35,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u44,axiom,
% 0.20/0.51      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u40,axiom,
% 0.20/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u32,negated_conjecture,
% 0.20/0.51      ~m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u104,negated_conjecture,
% 0.20/0.51      v1_xboole_0(sK2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u73,negated_conjecture,
% 0.20/0.51      v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u38,axiom,
% 0.20/0.51      ~v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u39,axiom,
% 0.20/0.51      ~v1_xboole_0(X0) | ~v1_xboole_0(X1) | m1_subset_1(X1,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u46,axiom,
% 0.20/0.51      ~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u65,negated_conjecture,
% 0.20/0.51      r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u47,axiom,
% 0.20/0.51      r1_tarski(X1,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u71,negated_conjecture,
% 0.20/0.51      ~r1_tarski(u1_struct_0(sK0),X0) | r2_hidden(sK2,X0) | v1_xboole_0(u1_struct_0(sK1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u68,negated_conjecture,
% 0.20/0.51      ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | u1_struct_0(sK0) = u1_struct_0(sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u109,negated_conjecture,
% 0.20/0.51      ~r1_tarski(X1,sK2) | ~r2_hidden(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u112,negated_conjecture,
% 0.20/0.51      ~r1_tarski(X1,u1_struct_0(sK1)) | ~r2_hidden(X0,X1) | v1_xboole_0(u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u59,axiom,
% 0.20/0.51      ~r1_tarski(X0,u1_struct_0(X2)) | ~m1_pre_topc(X2,X1) | ~l1_pre_topc(X1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u43,axiom,
% 0.20/0.51      ~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1).
% 0.20/0.51  
% 0.20/0.51  cnf(u57,axiom,
% 0.20/0.51      ~r1_tarski(X2,X1) | r2_hidden(X0,X1) | ~m1_subset_1(X0,X2) | v1_xboole_0(X2)).
% 0.20/0.51  
% 0.20/0.51  % (24172)# SZS output end Saturation.
% 0.20/0.51  % (24172)------------------------------
% 0.20/0.51  % (24172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24172)Termination reason: Satisfiable
% 0.20/0.51  
% 0.20/0.51  % (24172)Memory used [KB]: 6140
% 0.20/0.51  % (24172)Time elapsed: 0.099 s
% 0.20/0.51  % (24172)------------------------------
% 0.20/0.51  % (24172)------------------------------
% 0.20/0.51  % (24150)Success in time 0.145 s
%------------------------------------------------------------------------------
