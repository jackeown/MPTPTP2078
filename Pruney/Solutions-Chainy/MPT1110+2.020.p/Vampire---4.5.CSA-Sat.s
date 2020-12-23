%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:09 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   28 (  28 expanded)
%              Number of leaves         :   28 (  28 expanded)
%              Depth                    :    0
%              Number of atoms          :  100 ( 100 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal clause size      :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u46,negated_conjecture,
    ( ~ r2_hidden(sK3(sK1,X0),u1_pre_topc(X0))
    | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(sK1))
    | ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | k9_subset_1(u1_struct_0(X0),sK2,k2_struct_0(X0)) != sK3(sK1,X0)
    | ~ l1_pre_topc(X0)
    | m1_pre_topc(X0,sK1) )).

cnf(u40,negated_conjecture,
    ( ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | r2_hidden(sK4(X0,sK1,sK2),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ m1_pre_topc(sK1,X0) )).

cnf(u42,negated_conjecture,
    ( ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | m1_subset_1(sK4(X0,sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ m1_pre_topc(sK1,X0) )).

cnf(u44,negated_conjecture,
    ( ~ r2_hidden(sK2,u1_pre_topc(sK1))
    | sK2 = k9_subset_1(u1_struct_0(sK1),sK4(X0,sK1,sK2),k2_struct_0(sK1))
    | ~ l1_pre_topc(X0)
    | ~ m1_pre_topc(sK1,X0) )).

cnf(u16,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) )).

cnf(u28,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(X1) )).

cnf(u27,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X1)
    | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
    | ~ l1_pre_topc(X0) )).

cnf(u34,negated_conjecture,
    ( l1_pre_topc(sK1) )).

cnf(u17,negated_conjecture,
    ( l1_pre_topc(sK0) )).

cnf(u54,negated_conjecture,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK0))) )).

cnf(u14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) )).

cnf(u32,axiom,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,u1_pre_topc(X0))
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,X0) )).

cnf(u23,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | r2_hidden(sK4(X0,X1,X2),u1_pre_topc(X0))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,X0) )).

cnf(u22,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,X0) )).

cnf(u24,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,X0) )).

cnf(u18,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ r2_hidden(X3,u1_pre_topc(X0))
    | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK3(X0,X1)
    | ~ r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
    | m1_pre_topc(X1,X0) )).

cnf(u30,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u15,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u38,negated_conjecture,
    ( r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0)) )).

cnf(u35,negated_conjecture,
    ( r1_tarski(sK2,u1_struct_0(sK1)) )).

cnf(u47,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK1),X0)
    | r1_tarski(sK2,X0) )).

cnf(u53,negated_conjecture,
    ( ~ r1_tarski(k2_struct_0(sK0),X0)
    | r1_tarski(k2_struct_0(sK1),X0) )).

cnf(u26,axiom,
    ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(X1,X0) )).

cnf(u20,axiom,
    ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | r2_hidden(sK5(X0,X1),u1_pre_topc(X0))
    | r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
    | m1_pre_topc(X1,X0) )).

cnf(u19,axiom,
    ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
    | m1_pre_topc(X1,X0) )).

cnf(u21,axiom,
    ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | sK3(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))
    | r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
    | m1_pre_topc(X1,X0) )).

cnf(u29,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u31,axiom,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:55:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (13564)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (13565)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (13574)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (13566)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (13563)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (13572)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (13573)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (13563)Refutation not found, incomplete strategy% (13563)------------------------------
% 0.21/0.48  % (13563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13581)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (13569)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (13581)# SZS output start Saturation.
% 0.21/0.49  cnf(u46,negated_conjecture,
% 0.21/0.49      ~r2_hidden(sK3(sK1,X0),u1_pre_topc(X0)) | ~r1_tarski(k2_struct_0(X0),k2_struct_0(sK1)) | ~r2_hidden(sK2,u1_pre_topc(sK1)) | k9_subset_1(u1_struct_0(X0),sK2,k2_struct_0(X0)) != sK3(sK1,X0) | ~l1_pre_topc(X0) | m1_pre_topc(X0,sK1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u40,negated_conjecture,
% 0.21/0.49      ~r2_hidden(sK2,u1_pre_topc(sK1)) | r2_hidden(sK4(X0,sK1,sK2),u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u42,negated_conjecture,
% 0.21/0.49      ~r2_hidden(sK2,u1_pre_topc(sK1)) | m1_subset_1(sK4(X0,sK1,sK2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u44,negated_conjecture,
% 0.21/0.49      ~r2_hidden(sK2,u1_pre_topc(sK1)) | sK2 = k9_subset_1(u1_struct_0(sK1),sK4(X0,sK1,sK2),k2_struct_0(sK1)) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u16,negated_conjecture,
% 0.21/0.49      m1_pre_topc(sK1,sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u28,axiom,
% 0.21/0.49      ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u27,axiom,
% 0.21/0.49      ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u34,negated_conjecture,
% 0.21/0.49      l1_pre_topc(sK1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u17,negated_conjecture,
% 0.21/0.49      l1_pre_topc(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u54,negated_conjecture,
% 0.21/0.49      m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK0)))).
% 0.21/0.49  
% 0.21/0.49  cnf(u14,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))).
% 0.21/0.49  
% 0.21/0.49  cnf(u32,axiom,
% 0.21/0.49      ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X3,u1_pre_topc(X0)) | r2_hidden(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u23,axiom,
% 0.21/0.49      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | r2_hidden(sK4(X0,X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u22,axiom,
% 0.21/0.49      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u24,axiom,
% 0.21/0.49      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2 | ~r2_hidden(X2,u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u18,axiom,
% 0.21/0.49      ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~r2_hidden(X3,u1_pre_topc(X0)) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK3(X0,X1) | ~r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u30,axiom,
% 0.21/0.49      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u15,negated_conjecture,
% 0.21/0.49      ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.49  
% 0.21/0.49  cnf(u38,negated_conjecture,
% 0.21/0.49      r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u35,negated_conjecture,
% 0.21/0.49      r1_tarski(sK2,u1_struct_0(sK1))).
% 0.21/0.49  
% 0.21/0.49  cnf(u47,negated_conjecture,
% 0.21/0.49      ~r1_tarski(u1_struct_0(sK1),X0) | r1_tarski(sK2,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u53,negated_conjecture,
% 0.21/0.49      ~r1_tarski(k2_struct_0(sK0),X0) | r1_tarski(k2_struct_0(sK1),X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u26,axiom,
% 0.21/0.49      ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | m1_pre_topc(X1,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u20,axiom,
% 0.21/0.49      ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | r2_hidden(sK5(X0,X1),u1_pre_topc(X0)) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u19,axiom,
% 0.21/0.49      ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u21,axiom,
% 0.21/0.49      ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | sK3(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1)) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u29,axiom,
% 0.21/0.49      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 0.21/0.49  
% 0.21/0.49  cnf(u31,axiom,
% 0.21/0.49      ~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)).
% 0.21/0.49  
% 0.21/0.49  % (13581)# SZS output end Saturation.
% 0.21/0.49  % (13581)------------------------------
% 0.21/0.49  % (13581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13581)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (13581)Memory used [KB]: 1663
% 0.21/0.49  % (13581)Time elapsed: 0.084 s
% 0.21/0.49  % (13581)------------------------------
% 0.21/0.49  % (13581)------------------------------
% 0.21/0.49  % (13559)Success in time 0.13 s
%------------------------------------------------------------------------------
