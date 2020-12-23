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

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   31 (  31 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    0
%              Number of atoms          :  103 ( 103 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u19,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) )).

cnf(u31,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(X1) )).

cnf(u30,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X1)
    | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
    | ~ l1_pre_topc(X0) )).

cnf(u41,negated_conjecture,
    ( l1_pre_topc(sK1) )).

cnf(u20,negated_conjecture,
    ( l1_pre_topc(sK0) )).

cnf(u46,negated_conjecture,
    ( r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0)) )).

cnf(u29,axiom,
    ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(X1,X0) )).

cnf(u23,axiom,
    ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | r2_hidden(sK5(X0,X1),u1_pre_topc(X0))
    | r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
    | m1_pre_topc(X1,X0) )).

cnf(u22,axiom,
    ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
    | m1_pre_topc(X1,X0) )).

cnf(u24,axiom,
    ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | sK3(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))
    | r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
    | m1_pre_topc(X1,X0) )).

cnf(u36,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u56,negated_conjecture,
    ( r2_hidden(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0))) )).

cnf(u43,negated_conjecture,
    ( r2_hidden(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) )).

cnf(u34,axiom,
    ( ~ r2_hidden(X1,X0)
    | v1_xboole_0(X0)
    | m1_subset_1(X1,X0) )).

cnf(u38,axiom,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2) )).

cnf(u51,negated_conjecture,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK0))) )).

cnf(u17,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) )).

cnf(u18,negated_conjecture,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u39,axiom,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,u1_pre_topc(X0))
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,X0) )).

cnf(u52,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X0))
    | v1_xboole_0(u1_struct_0(sK1))
    | m1_subset_1(sK2,X0) )).

cnf(u58,negated_conjecture,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_struct_0(sK0)),k1_zfmisc_1(X0))
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0)))
    | m1_subset_1(k2_struct_0(sK1),X0) )).

cnf(u26,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | r2_hidden(sK4(X0,X1,X2),u1_pre_topc(X0))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,X0) )).

cnf(u25,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,X0) )).

cnf(u27,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,X0) )).

cnf(u21,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ r2_hidden(X3,u1_pre_topc(X0))
    | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK3(X0,X1)
    | ~ r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
    | m1_pre_topc(X1,X0) )).

cnf(u37,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u33,axiom,
    ( ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(X0) )).

cnf(u35,axiom,
    ( ~ m1_subset_1(X1,X0)
    | r2_hidden(X1,X0)
    | v1_xboole_0(X0) )).

cnf(u57,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK1)) )).

cnf(u42,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(sK2) )).

cnf(u32,axiom,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | m1_subset_1(X1,X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:20:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (19435)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (19442)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (19434)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (19442)Refutation not found, incomplete strategy% (19442)------------------------------
% 0.21/0.48  % (19442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (19442)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (19442)Memory used [KB]: 10618
% 0.21/0.48  % (19442)Time elapsed: 0.008 s
% 0.21/0.48  % (19442)------------------------------
% 0.21/0.48  % (19442)------------------------------
% 0.21/0.49  % (19447)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (19431)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (19434)Refutation not found, incomplete strategy% (19434)------------------------------
% 0.21/0.49  % (19434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19434)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (19434)Memory used [KB]: 10746
% 0.21/0.49  % (19434)Time elapsed: 0.029 s
% 0.21/0.49  % (19434)------------------------------
% 0.21/0.49  % (19434)------------------------------
% 0.21/0.49  % (19438)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (19428)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (19432)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (19433)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (19428)Refutation not found, incomplete strategy% (19428)------------------------------
% 0.21/0.50  % (19428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19428)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (19428)Memory used [KB]: 6140
% 0.21/0.50  % (19428)Time elapsed: 0.079 s
% 0.21/0.50  % (19428)------------------------------
% 0.21/0.50  % (19428)------------------------------
% 0.21/0.50  % (19448)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (19444)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (19448)Refutation not found, incomplete strategy% (19448)------------------------------
% 0.21/0.50  % (19448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19430)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (19429)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (19429)Refutation not found, incomplete strategy% (19429)------------------------------
% 0.21/0.50  % (19429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19429)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (19429)Memory used [KB]: 10618
% 0.21/0.50  % (19429)Time elapsed: 0.095 s
% 0.21/0.50  % (19429)------------------------------
% 0.21/0.50  % (19429)------------------------------
% 0.21/0.51  % (19437)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (19446)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (19445)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (19445)# SZS output start Saturation.
% 0.21/0.51  cnf(u19,negated_conjecture,
% 0.21/0.51      m1_pre_topc(sK1,sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u31,axiom,
% 0.21/0.51      ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u30,axiom,
% 0.21/0.51      ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u41,negated_conjecture,
% 0.21/0.51      l1_pre_topc(sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u20,negated_conjecture,
% 0.21/0.51      l1_pre_topc(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u46,negated_conjecture,
% 0.21/0.51      r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u29,axiom,
% 0.21/0.51      ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | m1_pre_topc(X1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u23,axiom,
% 0.21/0.51      ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | r2_hidden(sK5(X0,X1),u1_pre_topc(X0)) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u22,axiom,
% 0.21/0.51      ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u24,axiom,
% 0.21/0.51      ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | sK3(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1)) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u36,axiom,
% 0.21/0.51      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 0.21/0.51  
% 0.21/0.51  cnf(u56,negated_conjecture,
% 0.21/0.51      r2_hidden(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK0))) | v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u43,negated_conjecture,
% 0.21/0.51      r2_hidden(sK2,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))).
% 0.21/0.51  
% 0.21/0.51  cnf(u34,axiom,
% 0.21/0.51      ~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u38,axiom,
% 0.21/0.51      ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u51,negated_conjecture,
% 0.21/0.51      m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u17,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.21/0.51  
% 0.21/0.51  cnf(u18,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u39,axiom,
% 0.21/0.51      ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X3,u1_pre_topc(X0)) | r2_hidden(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u52,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X0)) | v1_xboole_0(u1_struct_0(sK1)) | m1_subset_1(sK2,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u58,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(k1_zfmisc_1(k2_struct_0(sK0)),k1_zfmisc_1(X0)) | v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_struct_0(sK1),X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u26,axiom,
% 0.21/0.51      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | r2_hidden(sK4(X0,X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u25,axiom,
% 0.21/0.51      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u27,axiom,
% 0.21/0.51      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2 | ~r2_hidden(X2,u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u21,axiom,
% 0.21/0.51      ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~r2_hidden(X3,u1_pre_topc(X0)) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK3(X0,X1) | ~r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u37,axiom,
% 0.21/0.51      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u33,axiom,
% 0.21/0.51      ~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u35,axiom,
% 0.21/0.51      ~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u57,negated_conjecture,
% 0.21/0.51      ~v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK1))).
% 0.21/0.51  
% 0.21/0.51  cnf(u42,negated_conjecture,
% 0.21/0.51      ~v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u32,axiom,
% 0.21/0.51      ~v1_xboole_0(X0) | ~v1_xboole_0(X1) | m1_subset_1(X1,X0)).
% 0.21/0.51  
% 0.21/0.51  % (19445)# SZS output end Saturation.
% 0.21/0.51  % (19445)------------------------------
% 0.21/0.51  % (19445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19445)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (19445)Memory used [KB]: 1663
% 0.21/0.51  % (19445)Time elapsed: 0.099 s
% 0.21/0.51  % (19445)------------------------------
% 0.21/0.51  % (19445)------------------------------
% 0.21/0.51  % (19427)Success in time 0.15 s
%------------------------------------------------------------------------------
