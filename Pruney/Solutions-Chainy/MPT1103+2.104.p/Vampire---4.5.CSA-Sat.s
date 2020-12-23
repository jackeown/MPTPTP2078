%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:47 EST 2020

% Result     : CounterSatisfiable 1.34s
% Output     : Saturation 1.34s
% Verified   : 
% Statistics : Number of clauses        :   23 (  23 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    0
%              Number of atoms          :   32 (  32 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u21,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u25,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u35,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u50,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u29,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u36,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u37,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u32,axiom,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 )).

cnf(u53,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u51,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u39,negated_conjecture,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) )).

cnf(u52,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u38,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u43,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u22,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u47,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u46,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

cnf(u18,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u41,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u23,axiom,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 )).

cnf(u34,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:13:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.50  % (30295)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.50  % (30314)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.50  % (30287)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.51  % (30295)Refutation not found, incomplete strategy% (30295)------------------------------
% 0.19/0.51  % (30295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (30306)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.51  % (30298)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.51  % (30294)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.51  % (30291)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.51  % (30308)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.51  % (30293)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.51  % (30298)Refutation not found, incomplete strategy% (30298)------------------------------
% 0.19/0.51  % (30298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (30298)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (30298)Memory used [KB]: 6268
% 0.19/0.51  % (30298)Time elapsed: 0.105 s
% 0.19/0.51  % (30298)------------------------------
% 0.19/0.51  % (30298)------------------------------
% 0.19/0.51  % (30308)Refutation not found, incomplete strategy% (30308)------------------------------
% 0.19/0.51  % (30308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (30308)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (30308)Memory used [KB]: 10618
% 0.19/0.51  % (30308)Time elapsed: 0.068 s
% 0.19/0.51  % (30308)------------------------------
% 0.19/0.51  % (30308)------------------------------
% 0.19/0.52  % (30300)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.34/0.52  % (30306)Refutation not found, incomplete strategy% (30306)------------------------------
% 1.34/0.52  % (30306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.52  % (30306)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.52  
% 1.34/0.52  % (30306)Memory used [KB]: 10746
% 1.34/0.52  % (30306)Time elapsed: 0.115 s
% 1.34/0.52  % (30306)------------------------------
% 1.34/0.52  % (30306)------------------------------
% 1.34/0.52  % (30290)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.34/0.52  % (30311)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.34/0.52  % (30290)Refutation not found, incomplete strategy% (30290)------------------------------
% 1.34/0.52  % (30290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.52  % (30290)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.52  
% 1.34/0.52  % (30290)Memory used [KB]: 6140
% 1.34/0.52  % (30290)Time elapsed: 0.118 s
% 1.34/0.52  % (30290)------------------------------
% 1.34/0.52  % (30290)------------------------------
% 1.34/0.52  % (30311)Refutation not found, incomplete strategy% (30311)------------------------------
% 1.34/0.52  % (30311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.52  % (30311)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.52  
% 1.34/0.52  % (30311)Memory used [KB]: 6268
% 1.34/0.52  % (30311)Time elapsed: 0.119 s
% 1.34/0.52  % (30311)------------------------------
% 1.34/0.52  % (30311)------------------------------
% 1.34/0.52  % (30313)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.52  % (30289)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.34/0.52  % (30295)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.52  
% 1.34/0.52  % (30295)Memory used [KB]: 10618
% 1.34/0.52  % (30295)Time elapsed: 0.104 s
% 1.34/0.52  % (30295)------------------------------
% 1.34/0.52  % (30295)------------------------------
% 1.34/0.53  % (30289)Refutation not found, incomplete strategy% (30289)------------------------------
% 1.34/0.53  % (30289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (30289)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (30289)Memory used [KB]: 10746
% 1.34/0.53  % (30288)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.34/0.53  % (30289)Time elapsed: 0.127 s
% 1.34/0.53  % (30289)------------------------------
% 1.34/0.53  % (30289)------------------------------
% 1.34/0.53  % (30315)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.34/0.53  % (30309)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.34/0.53  % (30286)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.53  % (30288)Refutation not found, incomplete strategy% (30288)------------------------------
% 1.34/0.53  % (30288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (30288)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (30288)Memory used [KB]: 10746
% 1.34/0.53  % (30288)Time elapsed: 0.126 s
% 1.34/0.53  % (30288)------------------------------
% 1.34/0.53  % (30288)------------------------------
% 1.34/0.53  % (30286)Refutation not found, incomplete strategy% (30286)------------------------------
% 1.34/0.53  % (30286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (30286)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (30286)Memory used [KB]: 1663
% 1.34/0.53  % (30286)Time elapsed: 0.126 s
% 1.34/0.53  % (30286)------------------------------
% 1.34/0.53  % (30286)------------------------------
% 1.34/0.53  % (30292)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.34/0.53  % (30294)Refutation not found, incomplete strategy% (30294)------------------------------
% 1.34/0.53  % (30294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (30294)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (30294)Memory used [KB]: 10618
% 1.34/0.53  % (30294)Time elapsed: 0.127 s
% 1.34/0.53  % (30294)------------------------------
% 1.34/0.53  % (30294)------------------------------
% 1.34/0.53  % (30305)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.53  % (30293)Refutation not found, incomplete strategy% (30293)------------------------------
% 1.34/0.53  % (30293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (30293)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (30293)Memory used [KB]: 6268
% 1.34/0.53  % (30293)Time elapsed: 0.124 s
% 1.34/0.53  % (30293)------------------------------
% 1.34/0.53  % (30293)------------------------------
% 1.34/0.53  % SZS status CounterSatisfiable for theBenchmark
% 1.34/0.53  % (30292)# SZS output start Saturation.
% 1.34/0.53  cnf(u21,negated_conjecture,
% 1.34/0.53      l1_struct_0(sK0)).
% 1.34/0.53  
% 1.34/0.53  cnf(u25,axiom,
% 1.34/0.53      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 1.34/0.53  
% 1.34/0.53  cnf(u35,axiom,
% 1.34/0.53      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.34/0.53  
% 1.34/0.53  cnf(u20,negated_conjecture,
% 1.34/0.53      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.34/0.53  
% 1.34/0.53  cnf(u50,negated_conjecture,
% 1.34/0.53      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 1.34/0.53  
% 1.34/0.53  cnf(u29,axiom,
% 1.34/0.53      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 1.34/0.53  
% 1.34/0.53  cnf(u42,axiom,
% 1.34/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 1.34/0.53  
% 1.34/0.53  cnf(u36,negated_conjecture,
% 1.34/0.53      r1_tarski(sK1,u1_struct_0(sK0))).
% 1.34/0.53  
% 1.34/0.53  cnf(u37,axiom,
% 1.34/0.53      r1_tarski(X0,X0)).
% 1.34/0.53  
% 1.34/0.53  cnf(u32,axiom,
% 1.34/0.53      ~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0).
% 1.34/0.53  
% 1.34/0.53  cnf(u53,negated_conjecture,
% 1.34/0.53      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 1.34/0.53  
% 1.34/0.53  cnf(u51,negated_conjecture,
% 1.34/0.53      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 1.34/0.53  
% 1.34/0.53  cnf(u39,negated_conjecture,
% 1.34/0.53      sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))).
% 1.34/0.53  
% 1.34/0.53  cnf(u52,negated_conjecture,
% 1.34/0.53      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 1.34/0.53  
% 1.34/0.53  cnf(u38,axiom,
% 1.34/0.53      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 1.34/0.53  
% 1.34/0.53  cnf(u43,negated_conjecture,
% 1.34/0.53      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 1.34/0.53  
% 1.34/0.53  cnf(u22,axiom,
% 1.34/0.53      k2_subset_1(X0) = X0).
% 1.34/0.53  
% 1.34/0.53  cnf(u47,axiom,
% 1.34/0.53      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 1.34/0.53  
% 1.34/0.53  cnf(u46,negated_conjecture,
% 1.34/0.53      k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0))).
% 1.34/0.53  
% 1.34/0.53  cnf(u18,negated_conjecture,
% 1.34/0.53      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 1.34/0.53  
% 1.34/0.53  cnf(u41,axiom,
% 1.34/0.53      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 1.34/0.53  
% 1.34/0.53  cnf(u23,axiom,
% 1.34/0.53      k5_xboole_0(X0,X0) = k1_xboole_0).
% 1.34/0.53  
% 1.34/0.53  cnf(u34,negated_conjecture,
% 1.34/0.53      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.34/0.53  
% 1.34/0.53  % (30292)# SZS output end Saturation.
% 1.34/0.53  % (30292)------------------------------
% 1.34/0.53  % (30292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (30292)Termination reason: Satisfiable
% 1.34/0.53  
% 1.34/0.53  % (30292)Memory used [KB]: 6268
% 1.34/0.53  % (30292)Time elapsed: 0.091 s
% 1.34/0.53  % (30292)------------------------------
% 1.34/0.53  % (30292)------------------------------
% 1.34/0.53  % (30291)Refutation not found, incomplete strategy% (30291)------------------------------
% 1.34/0.53  % (30291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (30291)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (30291)Memory used [KB]: 6268
% 1.34/0.53  % (30291)Time elapsed: 0.126 s
% 1.34/0.53  % (30291)------------------------------
% 1.34/0.53  % (30291)------------------------------
% 1.34/0.53  % (30312)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.53  % (30285)Success in time 0.176 s
%------------------------------------------------------------------------------
