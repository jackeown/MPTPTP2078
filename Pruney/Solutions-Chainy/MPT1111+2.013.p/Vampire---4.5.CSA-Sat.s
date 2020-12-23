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
% DateTime   : Thu Dec  3 13:09:11 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    0
%              Number of atoms          :   22 (  22 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u34,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u33,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ r2_hidden(X2,k1_xboole_0) )).

cnf(u25,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK2(X0),X1)
    | v1_xboole_0(X0) )).

cnf(u19,axiom,
    ( r2_hidden(sK2(X0),X0)
    | v1_xboole_0(X0) )).

cnf(u37,negated_conjecture,
    ( ~ r2_hidden(sK2(k1_xboole_0),k1_xboole_0) )).

cnf(u20,axiom,
    ( ~ r2_hidden(X1,X0)
    | ~ v1_xboole_0(X0) )).

cnf(u22,axiom,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2) )).

cnf(u18,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u21,axiom,
    ( ~ v1_xboole_0(X0)
    | X0 = X1
    | ~ v1_xboole_0(X1) )).

cnf(u24,axiom,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 )).

cnf(u31,negated_conjecture,
    ( k1_xboole_0 = sK1 )).

cnf(u35,negated_conjecture,
    ( k1_xboole_0 != k1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:00:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.45  % (1759)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.45  % (1759)Refutation not found, incomplete strategy% (1759)------------------------------
% 0.20/0.45  % (1759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (1759)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (1759)Memory used [KB]: 1535
% 0.20/0.45  % (1759)Time elapsed: 0.048 s
% 0.20/0.45  % (1759)------------------------------
% 0.20/0.45  % (1759)------------------------------
% 0.20/0.46  % (1753)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (1753)Refutation not found, incomplete strategy% (1753)------------------------------
% 0.20/0.47  % (1753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (1753)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (1753)Memory used [KB]: 6140
% 0.20/0.47  % (1753)Time elapsed: 0.069 s
% 0.20/0.47  % (1753)------------------------------
% 0.20/0.47  % (1753)------------------------------
% 0.20/0.47  % (1752)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.47  % (1751)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  % (1744)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (1750)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (1749)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (1757)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (1741)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (1748)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (1757)Refutation not found, incomplete strategy% (1757)------------------------------
% 0.20/0.49  % (1757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1757)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1757)Memory used [KB]: 10618
% 0.20/0.49  % (1757)Time elapsed: 0.069 s
% 0.20/0.49  % (1757)------------------------------
% 0.20/0.49  % (1757)------------------------------
% 0.20/0.49  % (1747)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (1741)Refutation not found, incomplete strategy% (1741)------------------------------
% 0.20/0.49  % (1741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1741)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1741)Memory used [KB]: 6012
% 0.20/0.49  % (1741)Time elapsed: 0.068 s
% 0.20/0.49  % (1741)------------------------------
% 0.20/0.49  % (1741)------------------------------
% 0.20/0.49  % (1743)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (1747)Refutation not found, incomplete strategy% (1747)------------------------------
% 0.20/0.49  % (1747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1747)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1747)Memory used [KB]: 10618
% 0.20/0.49  % (1747)Time elapsed: 0.046 s
% 0.20/0.49  % (1747)------------------------------
% 0.20/0.49  % (1747)------------------------------
% 0.20/0.49  % (1743)Refutation not found, incomplete strategy% (1743)------------------------------
% 0.20/0.49  % (1743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1743)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1743)Memory used [KB]: 10490
% 0.20/0.49  % (1743)Time elapsed: 0.086 s
% 0.20/0.49  % (1743)------------------------------
% 0.20/0.49  % (1743)------------------------------
% 0.20/0.49  % (1761)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (1744)Refutation not found, incomplete strategy% (1744)------------------------------
% 0.20/0.49  % (1744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1744)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1744)Memory used [KB]: 10490
% 0.20/0.49  % (1744)Time elapsed: 0.082 s
% 0.20/0.49  % (1744)------------------------------
% 0.20/0.49  % (1744)------------------------------
% 0.20/0.49  % (1761)Refutation not found, incomplete strategy% (1761)------------------------------
% 0.20/0.49  % (1761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1761)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1761)Memory used [KB]: 10490
% 0.20/0.49  % (1761)Time elapsed: 0.101 s
% 0.20/0.49  % (1761)------------------------------
% 0.20/0.49  % (1761)------------------------------
% 0.20/0.49  % (1745)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (1750)Refutation not found, incomplete strategy% (1750)------------------------------
% 0.20/0.49  % (1750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1750)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1750)Memory used [KB]: 10618
% 0.20/0.49  % (1750)Time elapsed: 0.088 s
% 0.20/0.49  % (1750)------------------------------
% 0.20/0.49  % (1750)------------------------------
% 0.20/0.50  % (1756)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (1742)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (1746)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (1756)Refutation not found, incomplete strategy% (1756)------------------------------
% 0.20/0.50  % (1756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1756)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (1756)Memory used [KB]: 6140
% 0.20/0.50  % (1756)Time elapsed: 0.086 s
% 0.20/0.50  % (1756)------------------------------
% 0.20/0.50  % (1756)------------------------------
% 0.20/0.50  % (1742)Refutation not found, incomplete strategy% (1742)------------------------------
% 0.20/0.50  % (1742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1742)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (1742)Memory used [KB]: 10490
% 0.20/0.50  % (1742)Time elapsed: 0.086 s
% 0.20/0.50  % (1742)------------------------------
% 0.20/0.50  % (1742)------------------------------
% 0.20/0.50  % (1752)Refutation not found, incomplete strategy% (1752)------------------------------
% 0.20/0.50  % (1752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1752)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (1752)Memory used [KB]: 10490
% 0.20/0.50  % (1752)Time elapsed: 0.107 s
% 0.20/0.50  % (1752)------------------------------
% 0.20/0.50  % (1752)------------------------------
% 0.20/0.50  % (1755)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  % (1755)Refutation not found, incomplete strategy% (1755)------------------------------
% 0.20/0.50  % (1755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1755)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (1755)Memory used [KB]: 10618
% 0.20/0.50  % (1755)Time elapsed: 0.054 s
% 0.20/0.50  % (1755)------------------------------
% 0.20/0.50  % (1755)------------------------------
% 0.20/0.50  % (1760)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (1754)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (1754)Refutation not found, incomplete strategy% (1754)------------------------------
% 0.20/0.50  % (1754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1754)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (1754)Memory used [KB]: 1663
% 0.20/0.50  % (1754)Time elapsed: 0.108 s
% 0.20/0.50  % (1754)------------------------------
% 0.20/0.50  % (1754)------------------------------
% 0.20/0.50  % (1758)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.50  % (1758)# SZS output start Saturation.
% 0.20/0.50  cnf(u34,negated_conjecture,
% 0.20/0.50      m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.50  
% 0.20/0.50  cnf(u33,negated_conjecture,
% 0.20/0.50      ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,k1_xboole_0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u25,axiom,
% 0.20/0.50      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK2(X0),X1) | v1_xboole_0(X0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u19,axiom,
% 0.20/0.50      r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u37,negated_conjecture,
% 0.20/0.50      ~r2_hidden(sK2(k1_xboole_0),k1_xboole_0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u20,axiom,
% 0.20/0.50      ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u22,axiom,
% 0.20/0.50      ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)).
% 0.20/0.50  
% 0.20/0.50  cnf(u18,axiom,
% 0.20/0.50      v1_xboole_0(k1_xboole_0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u21,axiom,
% 0.20/0.50      ~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)).
% 0.20/0.50  
% 0.20/0.50  cnf(u24,axiom,
% 0.20/0.50      ~v1_xboole_0(X0) | k1_xboole_0 = X0).
% 0.20/0.50  
% 0.20/0.50  cnf(u31,negated_conjecture,
% 0.20/0.50      k1_xboole_0 = sK1).
% 0.20/0.50  
% 0.20/0.50  cnf(u35,negated_conjecture,
% 0.20/0.50      k1_xboole_0 != k1_struct_0(sK0)).
% 0.20/0.50  
% 0.20/0.50  % (1758)# SZS output end Saturation.
% 0.20/0.50  % (1758)------------------------------
% 0.20/0.50  % (1758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1758)Termination reason: Satisfiable
% 0.20/0.50  
% 0.20/0.50  % (1758)Memory used [KB]: 1663
% 0.20/0.50  % (1758)Time elapsed: 0.107 s
% 0.20/0.50  % (1758)------------------------------
% 0.20/0.50  % (1758)------------------------------
% 0.20/0.51  % (1739)Success in time 0.158 s
%------------------------------------------------------------------------------
