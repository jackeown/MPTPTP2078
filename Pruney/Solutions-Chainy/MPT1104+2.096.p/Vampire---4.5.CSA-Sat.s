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
% DateTime   : Thu Dec  3 13:09:02 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   32 (  32 expanded)
%              Number of leaves         :   32 (  32 expanded)
%              Depth                    :    0
%              Number of atoms          :   42 (  42 expanded)
%              Number of equality atoms :   27 (  27 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u21,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u36,axiom,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) )).

cnf(u20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u28,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u34,negated_conjecture,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK2,X2) = k2_xboole_0(sK2,X2) )).

cnf(u35,negated_conjecture,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,X3) = k2_xboole_0(sK1,X3) )).

cnf(u24,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0)
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u26,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u27,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) )).

cnf(u33,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X1,X0) = k2_xboole_0(X1,X0) )).

cnf(u18,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u25,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 )).

cnf(u39,negated_conjecture,
    ( sK2 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK2)) )).

cnf(u48,negated_conjecture,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u40,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u47,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

cnf(u17,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u52,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u32,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X3) = k4_xboole_0(sK1,X3) )).

cnf(u31,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X2) = k4_xboole_0(sK2,X2) )).

cnf(u49,axiom,
    ( k4_subset_1(X0,X0,X0) = k2_xboole_0(X0,X0) )).

cnf(u51,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u50,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(u1_struct_0(sK0),sK2) )).

cnf(u44,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u46,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) )).

cnf(u41,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k2_xboole_0(sK2,u1_struct_0(sK0)) )).

cnf(u43,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1) )).

cnf(u42,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) )).

cnf(u22,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u30,axiom,
    ( k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u19,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:21:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (11355)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (11368)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (11363)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (11355)Refutation not found, incomplete strategy% (11355)------------------------------
% 0.22/0.50  % (11355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (11355)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (11355)Memory used [KB]: 10618
% 0.22/0.50  % (11355)Time elapsed: 0.070 s
% 0.22/0.50  % (11355)------------------------------
% 0.22/0.50  % (11355)------------------------------
% 0.22/0.50  % (11363)Refutation not found, incomplete strategy% (11363)------------------------------
% 0.22/0.50  % (11363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (11363)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (11363)Memory used [KB]: 10618
% 0.22/0.50  % (11363)Time elapsed: 0.071 s
% 0.22/0.50  % (11363)------------------------------
% 0.22/0.50  % (11363)------------------------------
% 0.22/0.50  % (11356)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (11356)Refutation not found, incomplete strategy% (11356)------------------------------
% 0.22/0.51  % (11356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (11356)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (11356)Memory used [KB]: 10618
% 0.22/0.51  % (11356)Time elapsed: 0.068 s
% 0.22/0.51  % (11356)------------------------------
% 0.22/0.51  % (11356)------------------------------
% 0.22/0.51  % (11360)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (11360)Refutation not found, incomplete strategy% (11360)------------------------------
% 0.22/0.51  % (11360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (11360)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (11360)Memory used [KB]: 10618
% 0.22/0.51  % (11360)Time elapsed: 0.084 s
% 0.22/0.51  % (11360)------------------------------
% 0.22/0.51  % (11360)------------------------------
% 0.22/0.51  % (11364)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (11362)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  % (11364)Refutation not found, incomplete strategy% (11364)------------------------------
% 0.22/0.52  % (11364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (11364)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (11364)Memory used [KB]: 6140
% 0.22/0.52  % (11364)Time elapsed: 0.084 s
% 0.22/0.52  % (11364)------------------------------
% 0.22/0.52  % (11364)------------------------------
% 0.22/0.52  % (11374)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (11354)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (11358)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.52  % (11354)Refutation not found, incomplete strategy% (11354)------------------------------
% 0.22/0.52  % (11354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (11354)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (11354)Memory used [KB]: 6140
% 0.22/0.52  % (11354)Time elapsed: 0.092 s
% 0.22/0.52  % (11354)------------------------------
% 0.22/0.52  % (11354)------------------------------
% 0.22/0.52  % (11357)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (11358)Refutation not found, incomplete strategy% (11358)------------------------------
% 0.22/0.52  % (11358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (11358)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (11358)Memory used [KB]: 1663
% 0.22/0.52  % (11358)Time elapsed: 0.096 s
% 0.22/0.52  % (11358)------------------------------
% 0.22/0.52  % (11358)------------------------------
% 0.22/0.52  % (11370)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.52  % (11359)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (11357)Refutation not found, incomplete strategy% (11357)------------------------------
% 0.22/0.53  % (11357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11357)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (11357)Memory used [KB]: 10618
% 0.22/0.53  % (11357)Time elapsed: 0.099 s
% 0.22/0.53  % (11357)------------------------------
% 0.22/0.53  % (11357)------------------------------
% 0.22/0.53  % (11365)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.53  % (11369)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.53  % (11370)Refutation not found, incomplete strategy% (11370)------------------------------
% 0.22/0.53  % (11370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11370)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (11370)Memory used [KB]: 10746
% 0.22/0.53  % (11370)Time elapsed: 0.089 s
% 0.22/0.53  % (11370)------------------------------
% 0.22/0.53  % (11370)------------------------------
% 0.22/0.53  % (11365)Refutation not found, incomplete strategy% (11365)------------------------------
% 0.22/0.53  % (11365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11365)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (11365)Memory used [KB]: 10618
% 0.22/0.53  % (11365)Time elapsed: 0.111 s
% 0.22/0.53  % (11365)------------------------------
% 0.22/0.53  % (11365)------------------------------
% 0.22/0.53  % (11369)Refutation not found, incomplete strategy% (11369)------------------------------
% 0.22/0.53  % (11369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11369)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (11369)Memory used [KB]: 6140
% 0.22/0.53  % (11369)Time elapsed: 0.063 s
% 0.22/0.53  % (11369)------------------------------
% 0.22/0.53  % (11369)------------------------------
% 0.22/0.53  % (11367)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.53  % (11367)Refutation not found, incomplete strategy% (11367)------------------------------
% 0.22/0.53  % (11367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11367)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (11367)Memory used [KB]: 1663
% 0.22/0.53  % (11367)Time elapsed: 0.106 s
% 0.22/0.53  % (11367)------------------------------
% 0.22/0.53  % (11367)------------------------------
% 0.22/0.53  % (11361)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.53  % (11373)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.53  % (11372)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.53  % (11366)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (11366)Refutation not found, incomplete strategy% (11366)------------------------------
% 0.22/0.54  % (11366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11366)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11366)Memory used [KB]: 6012
% 0.22/0.54  % (11366)Time elapsed: 0.001 s
% 0.22/0.54  % (11366)------------------------------
% 0.22/0.54  % (11366)------------------------------
% 0.22/0.54  % (11373)Refutation not found, incomplete strategy% (11373)------------------------------
% 0.22/0.54  % (11373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11373)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11373)Memory used [KB]: 6140
% 0.22/0.54  % (11373)Time elapsed: 0.111 s
% 0.22/0.54  % (11373)------------------------------
% 0.22/0.54  % (11373)------------------------------
% 0.22/0.54  % (11372)Refutation not found, incomplete strategy% (11372)------------------------------
% 0.22/0.54  % (11372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11372)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11372)Memory used [KB]: 1663
% 0.22/0.54  % (11372)Time elapsed: 0.108 s
% 0.22/0.54  % (11372)------------------------------
% 0.22/0.54  % (11372)------------------------------
% 0.22/0.54  % (11374)Refutation not found, incomplete strategy% (11374)------------------------------
% 0.22/0.54  % (11374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11374)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11374)Memory used [KB]: 10490
% 0.22/0.54  % (11374)Time elapsed: 0.117 s
% 0.22/0.54  % (11374)------------------------------
% 0.22/0.54  % (11374)------------------------------
% 0.22/0.54  % (11371)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.54  % (11371)# SZS output start Saturation.
% 0.22/0.54  cnf(u21,negated_conjecture,
% 0.22/0.54      l1_struct_0(sK0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u36,axiom,
% 0.22/0.54      ~l1_struct_0(X0) | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u20,negated_conjecture,
% 0.22/0.54      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u16,negated_conjecture,
% 0.22/0.54      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u28,axiom,
% 0.22/0.54      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u34,negated_conjecture,
% 0.22/0.54      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK2,X2) = k2_xboole_0(sK2,X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u35,negated_conjecture,
% 0.22/0.54      ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X3) = k2_xboole_0(sK1,X3)).
% 0.22/0.54  
% 0.22/0.54  cnf(u24,axiom,
% 0.22/0.54      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.22/0.54  
% 0.22/0.54  cnf(u26,axiom,
% 0.22/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u27,axiom,
% 0.22/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u33,axiom,
% 0.22/0.54      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k4_subset_1(X1,X1,X0) = k2_xboole_0(X1,X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u18,negated_conjecture,
% 0.22/0.54      r1_xboole_0(sK1,sK2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u25,axiom,
% 0.22/0.54      ~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0).
% 0.22/0.54  
% 0.22/0.54  cnf(u39,negated_conjecture,
% 0.22/0.54      sK2 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK2))).
% 0.22/0.54  
% 0.22/0.54  cnf(u48,negated_conjecture,
% 0.22/0.54      sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u40,negated_conjecture,
% 0.22/0.54      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u47,negated_conjecture,
% 0.22/0.54      k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u17,negated_conjecture,
% 0.22/0.54      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u52,negated_conjecture,
% 0.22/0.54      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u32,negated_conjecture,
% 0.22/0.54      k7_subset_1(u1_struct_0(sK0),sK1,X3) = k4_xboole_0(sK1,X3)).
% 0.22/0.54  
% 0.22/0.54  cnf(u31,negated_conjecture,
% 0.22/0.54      k7_subset_1(u1_struct_0(sK0),sK2,X2) = k4_xboole_0(sK2,X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u49,axiom,
% 0.22/0.54      k4_subset_1(X0,X0,X0) = k2_xboole_0(X0,X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u51,negated_conjecture,
% 0.22/0.54      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),sK1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u50,negated_conjecture,
% 0.22/0.54      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(u1_struct_0(sK0),sK2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u44,negated_conjecture,
% 0.22/0.54      k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,u1_struct_0(sK0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u46,negated_conjecture,
% 0.22/0.54      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u41,negated_conjecture,
% 0.22/0.54      k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k2_xboole_0(sK2,u1_struct_0(sK0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u43,negated_conjecture,
% 0.22/0.54      k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u42,negated_conjecture,
% 0.22/0.54      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u22,axiom,
% 0.22/0.54      k2_subset_1(X0) = X0).
% 0.22/0.54  
% 0.22/0.54  cnf(u30,axiom,
% 0.22/0.54      k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u19,negated_conjecture,
% 0.22/0.54      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.22/0.54  
% 0.22/0.54  % (11371)# SZS output end Saturation.
% 0.22/0.54  % (11371)------------------------------
% 0.22/0.54  % (11371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11371)Termination reason: Satisfiable
% 0.22/0.54  
% 0.22/0.54  % (11371)Memory used [KB]: 1663
% 0.22/0.54  % (11371)Time elapsed: 0.090 s
% 0.22/0.54  % (11371)------------------------------
% 0.22/0.54  % (11371)------------------------------
% 0.22/0.54  % (11353)Success in time 0.176 s
%------------------------------------------------------------------------------
