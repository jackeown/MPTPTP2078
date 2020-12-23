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
% DateTime   : Thu Dec  3 13:08:48 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   18 (  18 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    0
%              Number of atoms          :   23 (  23 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u35,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u21,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u30,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u31,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u36,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u37,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u29,axiom,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 )).

cnf(u43,axiom,
    ( k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u19,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u42,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u34,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u27,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) )).

cnf(u39,negated_conjecture,
    ( u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u25,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u38,axiom,
    ( k2_xboole_0(X0,X0) = X0 )).

cnf(u24,axiom,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u22,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u33,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (12389)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (12379)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (12378)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (12379)Refutation not found, incomplete strategy% (12379)------------------------------
% 0.20/0.51  % (12379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12405)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (12382)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (12381)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (12381)Refutation not found, incomplete strategy% (12381)------------------------------
% 0.20/0.51  % (12381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12381)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (12381)Memory used [KB]: 6140
% 0.20/0.51  % (12381)Time elapsed: 0.112 s
% 0.20/0.51  % (12381)------------------------------
% 0.20/0.51  % (12381)------------------------------
% 0.20/0.51  % (12394)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (12389)Refutation not found, incomplete strategy% (12389)------------------------------
% 0.20/0.51  % (12389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12389)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (12389)Memory used [KB]: 6268
% 0.20/0.51  % (12389)Time elapsed: 0.105 s
% 0.20/0.51  % (12389)------------------------------
% 0.20/0.51  % (12389)------------------------------
% 0.20/0.51  % (12394)Refutation not found, incomplete strategy% (12394)------------------------------
% 0.20/0.51  % (12394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12394)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (12394)Memory used [KB]: 10618
% 0.20/0.51  % (12394)Time elapsed: 0.112 s
% 0.20/0.51  % (12394)------------------------------
% 0.20/0.51  % (12394)------------------------------
% 0.20/0.51  % (12399)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (12399)Refutation not found, incomplete strategy% (12399)------------------------------
% 0.20/0.51  % (12399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12399)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (12399)Memory used [KB]: 10618
% 0.20/0.51  % (12399)Time elapsed: 0.076 s
% 0.20/0.51  % (12399)------------------------------
% 0.20/0.51  % (12399)------------------------------
% 0.20/0.51  % (12400)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (12400)Refutation not found, incomplete strategy% (12400)------------------------------
% 0.20/0.52  % (12400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12400)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (12400)Memory used [KB]: 1663
% 0.20/0.52  % (12400)Time elapsed: 0.112 s
% 0.20/0.52  % (12400)------------------------------
% 0.20/0.52  % (12400)------------------------------
% 0.20/0.52  % (12377)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (12384)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (12386)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (12397)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (12377)Refutation not found, incomplete strategy% (12377)------------------------------
% 0.20/0.52  % (12377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12377)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (12377)Memory used [KB]: 1663
% 0.20/0.52  % (12377)Time elapsed: 0.082 s
% 0.20/0.52  % (12377)------------------------------
% 0.20/0.52  % (12377)------------------------------
% 0.20/0.52  % (12386)Refutation not found, incomplete strategy% (12386)------------------------------
% 0.20/0.52  % (12386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12386)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (12386)Memory used [KB]: 10618
% 0.20/0.52  % (12386)Time elapsed: 0.114 s
% 0.20/0.52  % (12386)------------------------------
% 0.20/0.52  % (12386)------------------------------
% 0.20/0.52  % (12379)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (12379)Memory used [KB]: 10618
% 0.20/0.52  % (12379)Time elapsed: 0.102 s
% 0.20/0.52  % (12379)------------------------------
% 0.20/0.52  % (12379)------------------------------
% 0.20/0.52  % (12388)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (12380)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (12383)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (12397)Refutation not found, incomplete strategy% (12397)------------------------------
% 0.20/0.52  % (12397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12397)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (12397)Memory used [KB]: 10746
% 0.20/0.52  % (12397)Time elapsed: 0.113 s
% 0.20/0.52  % (12397)------------------------------
% 0.20/0.52  % (12397)------------------------------
% 0.20/0.52  % (12380)Refutation not found, incomplete strategy% (12380)------------------------------
% 0.20/0.52  % (12380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12380)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (12380)Memory used [KB]: 10618
% 0.20/0.52  % (12380)Time elapsed: 0.118 s
% 0.20/0.52  % (12380)------------------------------
% 0.20/0.52  % (12380)------------------------------
% 0.20/0.52  % (12398)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (12391)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (12396)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (12404)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (12403)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (12396)Refutation not found, incomplete strategy% (12396)------------------------------
% 0.20/0.52  % (12396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12396)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (12396)Memory used [KB]: 10746
% 0.20/0.52  % (12396)Time elapsed: 0.122 s
% 0.20/0.52  % (12396)------------------------------
% 0.20/0.52  % (12396)------------------------------
% 0.20/0.53  % (12388)Refutation not found, incomplete strategy% (12388)------------------------------
% 0.20/0.53  % (12388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (12388)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (12388)Memory used [KB]: 10618
% 0.20/0.53  % (12388)Time elapsed: 0.126 s
% 0.20/0.53  % (12388)------------------------------
% 0.20/0.53  % (12388)------------------------------
% 0.20/0.53  % (12385)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (12390)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (12385)Refutation not found, incomplete strategy% (12385)------------------------------
% 0.20/0.53  % (12385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (12385)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (12385)Memory used [KB]: 10618
% 0.20/0.53  % (12385)Time elapsed: 0.132 s
% 0.20/0.53  % (12385)------------------------------
% 0.20/0.53  % (12385)------------------------------
% 0.20/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.53  % (12383)# SZS output start Saturation.
% 0.20/0.53  cnf(u35,axiom,
% 0.20/0.53      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u21,negated_conjecture,
% 0.20/0.53      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.53  
% 0.20/0.53  cnf(u30,axiom,
% 0.20/0.53      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u31,axiom,
% 0.20/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u36,negated_conjecture,
% 0.20/0.53      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u37,axiom,
% 0.20/0.53      r1_tarski(X0,X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u29,axiom,
% 0.20/0.53      ~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1).
% 0.20/0.53  
% 0.20/0.53  cnf(u43,axiom,
% 0.20/0.53      k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u19,negated_conjecture,
% 0.20/0.53      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u42,negated_conjecture,
% 0.20/0.53      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u34,axiom,
% 0.20/0.53      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u27,axiom,
% 0.20/0.53      k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u39,negated_conjecture,
% 0.20/0.53      u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u25,axiom,
% 0.20/0.53      k4_xboole_0(X0,k1_xboole_0) = X0).
% 0.20/0.53  
% 0.20/0.53  cnf(u38,axiom,
% 0.20/0.53      k2_xboole_0(X0,X0) = X0).
% 0.20/0.53  
% 0.20/0.53  cnf(u24,axiom,
% 0.20/0.53      k2_xboole_0(X0,k1_xboole_0) = X0).
% 0.20/0.53  
% 0.20/0.53  cnf(u22,axiom,
% 0.20/0.53      k2_subset_1(X0) = X0).
% 0.20/0.53  
% 0.20/0.53  cnf(u33,negated_conjecture,
% 0.20/0.53      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.20/0.53  
% 0.20/0.53  % (12383)# SZS output end Saturation.
% 0.20/0.53  % (12383)------------------------------
% 0.20/0.53  % (12383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (12383)Termination reason: Satisfiable
% 0.20/0.53  
% 0.20/0.53  % (12383)Memory used [KB]: 6140
% 0.20/0.53  % (12383)Time elapsed: 0.102 s
% 0.20/0.53  % (12383)------------------------------
% 0.20/0.53  % (12383)------------------------------
% 0.20/0.53  % (12376)Success in time 0.164 s
%------------------------------------------------------------------------------
