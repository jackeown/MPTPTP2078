%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:13 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    0
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u21,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u20,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ r2_hidden(X2,k1_xboole_0) )).

cnf(u14,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k1_xboole_0 = X1
    | m1_subset_1(sK2(X0,X1),X0) )).

cnf(u15,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k1_xboole_0 = X1
    | r2_hidden(sK2(X0,X1),X1) )).

cnf(u19,negated_conjecture,
    ( k1_xboole_0 = sK1 )).

cnf(u22,negated_conjecture,
    ( k1_xboole_0 != k1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 13:43:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.43  % (3765)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.43  % (3765)Refutation not found, incomplete strategy% (3765)------------------------------
% 0.22/0.43  % (3765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (3765)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.43  
% 0.22/0.43  % (3765)Memory used [KB]: 6012
% 0.22/0.43  % (3765)Time elapsed: 0.003 s
% 0.22/0.43  % (3765)------------------------------
% 0.22/0.43  % (3765)------------------------------
% 0.22/0.46  % (3756)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.46  % (3756)Refutation not found, incomplete strategy% (3756)------------------------------
% 0.22/0.46  % (3756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (3756)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (3756)Memory used [KB]: 10618
% 0.22/0.46  % (3756)Time elapsed: 0.033 s
% 0.22/0.46  % (3756)------------------------------
% 0.22/0.46  % (3756)------------------------------
% 0.22/0.49  % (3769)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (3757)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (3757)Refutation not found, incomplete strategy% (3757)------------------------------
% 0.22/0.49  % (3757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (3757)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (3757)Memory used [KB]: 10618
% 0.22/0.49  % (3757)Time elapsed: 0.061 s
% 0.22/0.49  % (3757)------------------------------
% 0.22/0.49  % (3757)------------------------------
% 0.22/0.49  % (3771)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (3771)Refutation not found, incomplete strategy% (3771)------------------------------
% 0.22/0.49  % (3771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (3771)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (3771)Memory used [KB]: 10618
% 0.22/0.49  % (3771)Time elapsed: 0.063 s
% 0.22/0.49  % (3771)------------------------------
% 0.22/0.49  % (3771)------------------------------
% 0.22/0.50  % (3767)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (3767)Refutation not found, incomplete strategy% (3767)------------------------------
% 0.22/0.50  % (3767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (3767)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (3767)Memory used [KB]: 6012
% 0.22/0.50  % (3767)Time elapsed: 0.002 s
% 0.22/0.50  % (3767)------------------------------
% 0.22/0.50  % (3767)------------------------------
% 0.22/0.50  % (3760)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (3761)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (3763)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (3766)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (3766)Refutation not found, incomplete strategy% (3766)------------------------------
% 0.22/0.50  % (3766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (3766)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (3766)Memory used [KB]: 10490
% 0.22/0.50  % (3766)Time elapsed: 0.075 s
% 0.22/0.50  % (3766)------------------------------
% 0.22/0.50  % (3766)------------------------------
% 0.22/0.50  % (3759)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (3774)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (3768)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (3768)Refutation not found, incomplete strategy% (3768)------------------------------
% 0.22/0.51  % (3768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3768)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3768)Memory used [KB]: 1535
% 0.22/0.51  % (3768)Time elapsed: 0.079 s
% 0.22/0.51  % (3768)------------------------------
% 0.22/0.51  % (3768)------------------------------
% 0.22/0.51  % (3764)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (3764)Refutation not found, incomplete strategy% (3764)------------------------------
% 0.22/0.51  % (3764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3764)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  % (3775)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  
% 0.22/0.51  % (3764)Memory used [KB]: 10618
% 0.22/0.51  % (3764)Time elapsed: 0.087 s
% 0.22/0.51  % (3764)------------------------------
% 0.22/0.51  % (3764)------------------------------
% 0.22/0.51  % (3775)Refutation not found, incomplete strategy% (3775)------------------------------
% 0.22/0.51  % (3775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3775)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3775)Memory used [KB]: 10490
% 0.22/0.51  % (3775)Time elapsed: 0.088 s
% 0.22/0.51  % (3775)------------------------------
% 0.22/0.51  % (3775)------------------------------
% 0.22/0.51  % (3773)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (3773)Refutation not found, incomplete strategy% (3773)------------------------------
% 0.22/0.51  % (3773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3773)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3773)Memory used [KB]: 1535
% 0.22/0.51  % (3773)Time elapsed: 0.087 s
% 0.22/0.51  % (3773)------------------------------
% 0.22/0.51  % (3773)------------------------------
% 0.22/0.51  % (3761)Refutation not found, incomplete strategy% (3761)------------------------------
% 0.22/0.51  % (3761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3761)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3761)Memory used [KB]: 10618
% 0.22/0.51  % (3761)Time elapsed: 0.065 s
% 0.22/0.51  % (3761)------------------------------
% 0.22/0.51  % (3761)------------------------------
% 0.22/0.51  % (3758)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (3772)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (3758)Refutation not found, incomplete strategy% (3758)------------------------------
% 0.22/0.51  % (3758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3758)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3758)Memory used [KB]: 10618
% 0.22/0.51  % (3758)Time elapsed: 0.085 s
% 0.22/0.51  % (3758)------------------------------
% 0.22/0.51  % (3758)------------------------------
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (3772)# SZS output start Saturation.
% 0.22/0.51  cnf(u21,negated_conjecture,
% 0.22/0.51      m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.51  
% 0.22/0.51  cnf(u20,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,k1_xboole_0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u14,axiom,
% 0.22/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | m1_subset_1(sK2(X0,X1),X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u15,axiom,
% 0.22/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | r2_hidden(sK2(X0,X1),X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u19,negated_conjecture,
% 0.22/0.51      k1_xboole_0 = sK1).
% 0.22/0.51  
% 0.22/0.51  cnf(u22,negated_conjecture,
% 0.22/0.51      k1_xboole_0 != k1_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  % (3772)# SZS output end Saturation.
% 0.22/0.51  % (3772)------------------------------
% 0.22/0.51  % (3772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3772)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (3772)Memory used [KB]: 1663
% 0.22/0.51  % (3772)Time elapsed: 0.092 s
% 0.22/0.51  % (3772)------------------------------
% 0.22/0.51  % (3772)------------------------------
% 0.22/0.51  % (3755)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (3754)Success in time 0.141 s
%------------------------------------------------------------------------------
