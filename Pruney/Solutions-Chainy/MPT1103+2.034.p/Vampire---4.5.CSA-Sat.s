%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:38 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   33 (  33 expanded)
%              Number of leaves         :   33 (  33 expanded)
%              Depth                    :    0
%              Number of atoms          :   42 (  42 expanded)
%              Number of equality atoms :   32 (  32 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u24,negated_conjecture,
    ( l1_struct_0(sK0) )).

% (14283)Termination reason: Refutation not found, incomplete strategy
cnf(u30,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u42,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u27,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u150,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u62,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u61,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u154,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u151,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u43,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u153,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u100,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) )).

cnf(u69,axiom,
    ( k7_subset_1(X1,k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) )).

cnf(u59,axiom,
    ( k7_subset_1(X1,k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2)) )).

cnf(u67,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u71,axiom,
    ( k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0) )).

cnf(u63,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u64,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

cnf(u51,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0))) )).

cnf(u37,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u53,axiom,
    ( k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X1,X1)) )).

cnf(u46,axiom,
    ( k1_xboole_0 = k3_subset_1(X0,X0) )).

cnf(u72,axiom,
    ( k1_xboole_0 = k7_subset_1(X3,k1_xboole_0,k1_xboole_0) )).

cnf(u68,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

cnf(u152,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)) )).

cnf(u21,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u60,axiom,
    ( k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k3_xboole_0(X3,X4)) )).

cnf(u54,axiom,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 )).

cnf(u52,axiom,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 )).

cnf(u31,axiom,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

cnf(u41,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:31:05 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.54  % (14281)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (14283)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (14303)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (14280)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (14289)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (14295)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (14292)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (14280)Refutation not found, incomplete strategy% (14280)------------------------------
% 0.21/0.56  % (14280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (14280)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (14280)Memory used [KB]: 1791
% 0.21/0.56  % (14280)Time elapsed: 0.131 s
% 0.21/0.56  % (14280)------------------------------
% 0.21/0.56  % (14280)------------------------------
% 0.21/0.56  % (14295)Refutation not found, incomplete strategy% (14295)------------------------------
% 0.21/0.56  % (14295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (14295)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (14295)Memory used [KB]: 6140
% 0.21/0.56  % (14295)Time elapsed: 0.004 s
% 0.21/0.56  % (14295)------------------------------
% 0.21/0.56  % (14295)------------------------------
% 0.21/0.56  % (14303)Refutation not found, incomplete strategy% (14303)------------------------------
% 0.21/0.56  % (14303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (14303)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (14303)Memory used [KB]: 1791
% 0.21/0.56  % (14303)Time elapsed: 0.082 s
% 0.21/0.56  % (14303)------------------------------
% 0.21/0.56  % (14303)------------------------------
% 0.21/0.56  % (14282)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (14284)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.57  % (14284)Refutation not found, incomplete strategy% (14284)------------------------------
% 0.21/0.57  % (14284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (14284)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (14284)Memory used [KB]: 6268
% 0.21/0.57  % (14284)Time elapsed: 0.137 s
% 0.21/0.57  % (14284)------------------------------
% 0.21/0.57  % (14284)------------------------------
% 0.21/0.57  % (14282)Refutation not found, incomplete strategy% (14282)------------------------------
% 0.21/0.57  % (14282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (14282)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (14282)Memory used [KB]: 10746
% 0.21/0.57  % (14282)Time elapsed: 0.135 s
% 0.21/0.57  % (14282)------------------------------
% 0.21/0.57  % (14282)------------------------------
% 0.21/0.57  % (14287)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.57  % (14297)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.57  % (14304)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  % (14287)Refutation not found, incomplete strategy% (14287)------------------------------
% 0.21/0.57  % (14287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (14297)Refutation not found, incomplete strategy% (14297)------------------------------
% 0.21/0.57  % (14297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (14287)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (14287)Memory used [KB]: 6268
% 0.21/0.57  % (14287)Time elapsed: 0.092 s
% 0.21/0.57  % (14287)------------------------------
% 0.21/0.57  % (14287)------------------------------
% 0.21/0.58  % (14300)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.58  % (14289)Refutation not found, incomplete strategy% (14289)------------------------------
% 0.21/0.58  % (14289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (14289)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (14289)Memory used [KB]: 10746
% 0.21/0.58  % (14289)Time elapsed: 0.147 s
% 0.21/0.58  % (14289)------------------------------
% 0.21/0.58  % (14289)------------------------------
% 0.21/0.58  % (14283)Refutation not found, incomplete strategy% (14283)------------------------------
% 0.21/0.58  % (14283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (14296)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.58  % (14285)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (14286)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.58  % (14292)Refutation not found, incomplete strategy% (14292)------------------------------
% 0.21/0.58  % (14292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (14292)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (14292)Memory used [KB]: 6268
% 0.21/0.58  % (14292)Time elapsed: 0.149 s
% 0.21/0.58  % (14292)------------------------------
% 0.21/0.58  % (14292)------------------------------
% 0.21/0.58  % (14298)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.58  % (14285)Refutation not found, incomplete strategy% (14285)------------------------------
% 0.21/0.58  % (14285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (14285)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (14285)Memory used [KB]: 6268
% 0.21/0.58  % (14285)Time elapsed: 0.146 s
% 0.21/0.58  % (14285)------------------------------
% 0.21/0.58  % (14285)------------------------------
% 0.21/0.58  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.58  % (14286)# SZS output start Saturation.
% 0.21/0.58  cnf(u24,negated_conjecture,
% 0.21/0.58      l1_struct_0(sK0)).
% 0.21/0.58  
% 0.21/0.58  % (14283)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  cnf(u30,axiom,
% 0.21/0.58      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.21/0.58  
% 0.21/0.58  cnf(u42,axiom,
% 0.21/0.58      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.58  
% 0.21/0.58  cnf(u27,axiom,
% 0.21/0.58      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.21/0.58  
% 0.21/0.58  cnf(u23,negated_conjecture,
% 0.21/0.58      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.58  
% 0.21/0.58  cnf(u150,negated_conjecture,
% 0.21/0.58      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.21/0.58  
% 0.21/0.58  cnf(u34,axiom,
% 0.21/0.58      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.21/0.58  
% 0.21/0.58  cnf(u62,axiom,
% 0.21/0.58      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u61,axiom,
% 0.21/0.58      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.58  
% 0.21/0.58  cnf(u154,negated_conjecture,
% 0.21/0.58      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u151,negated_conjecture,
% 0.21/0.58      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.21/0.58  
% 0.21/0.58  cnf(u43,negated_conjecture,
% 0.21/0.58      sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.21/0.58  
% 0.21/0.58  cnf(u153,negated_conjecture,
% 0.21/0.58      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.58  
% 0.21/0.58  cnf(u100,axiom,
% 0.21/0.58      k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))).
% 0.21/0.58  
% 0.21/0.58  cnf(u69,axiom,
% 0.21/0.58      k7_subset_1(X1,k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0))).
% 0.21/0.58  
% 0.21/0.58  cnf(u59,axiom,
% 0.21/0.58      k7_subset_1(X1,k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2))).
% 0.21/0.58  
% 0.21/0.58  cnf(u67,axiom,
% 0.21/0.58      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 0.21/0.58  
% 0.21/0.58  cnf(u71,axiom,
% 0.21/0.58      k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u63,negated_conjecture,
% 0.21/0.58      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u64,negated_conjecture,
% 0.21/0.58      k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u51,negated_conjecture,
% 0.21/0.58      k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0)))).
% 0.21/0.58  
% 0.21/0.58  cnf(u37,axiom,
% 0.21/0.58      k3_subset_1(X0,k1_xboole_0) = X0).
% 0.21/0.58  
% 0.21/0.58  cnf(u53,axiom,
% 0.21/0.58      k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X1,X1))).
% 0.21/0.58  
% 0.21/0.58  cnf(u46,axiom,
% 0.21/0.58      k1_xboole_0 = k3_subset_1(X0,X0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u72,axiom,
% 0.21/0.58      k1_xboole_0 = k7_subset_1(X3,k1_xboole_0,k1_xboole_0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u68,axiom,
% 0.21/0.58      k1_xboole_0 = k7_subset_1(X1,X1,X1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u152,negated_conjecture,
% 0.21/0.58      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))).
% 0.21/0.58  
% 0.21/0.58  cnf(u21,negated_conjecture,
% 0.21/0.58      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u60,axiom,
% 0.21/0.58      k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k3_xboole_0(X3,X4))).
% 0.21/0.58  
% 0.21/0.58  cnf(u54,axiom,
% 0.21/0.58      k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0).
% 0.21/0.58  
% 0.21/0.58  cnf(u52,axiom,
% 0.21/0.58      k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0).
% 0.21/0.58  
% 0.21/0.58  cnf(u31,axiom,
% 0.21/0.58      k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u41,negated_conjecture,
% 0.21/0.58      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.58  
% 0.21/0.58  % (14286)# SZS output end Saturation.
% 0.21/0.58  % (14286)------------------------------
% 0.21/0.58  % (14286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (14286)Termination reason: Satisfiable
% 0.21/0.58  
% 0.21/0.58  % (14286)Memory used [KB]: 6268
% 0.21/0.58  % (14286)Time elapsed: 0.149 s
% 0.21/0.58  % (14286)------------------------------
% 0.21/0.58  % (14286)------------------------------
% 0.21/0.58  
% 0.21/0.58  % (14283)Memory used [KB]: 10746
% 0.21/0.58  % (14283)Time elapsed: 0.146 s
% 0.21/0.58  % (14283)------------------------------
% 0.21/0.58  % (14283)------------------------------
% 0.21/0.58  % (14279)Success in time 0.214 s
%------------------------------------------------------------------------------
