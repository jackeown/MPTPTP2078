%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:47 EST 2020

% Result     : CounterSatisfiable 1.50s
% Output     : Saturation 1.50s
% Verified   : 
% Statistics : Number of clauses        :   24 (  24 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    0
%              Number of atoms          :   32 (  32 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u23,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u28,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u43,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u86,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

% (5846)Refutation not found, incomplete strategy% (5846)------------------------------
% (5846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
cnf(u59,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u24,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

% (5846)Termination reason: Refutation not found, incomplete strategy

cnf(u40,axiom,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 )).

% (5846)Memory used [KB]: 10874
cnf(u44,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) )).

% (5846)Time elapsed: 0.146 s
cnf(u89,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

% (5846)------------------------------
% (5846)------------------------------
cnf(u87,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u88,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u61,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u65,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1) )).

cnf(u71,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))) )).

cnf(u64,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u20,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u58,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u60,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) )).

cnf(u51,axiom,
    ( k1_xboole_0 = k5_xboole_0(X1,X1) )).

cnf(u38,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u26,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u25,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u42,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:55:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (5828)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (5844)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (5828)Refutation not found, incomplete strategy% (5828)------------------------------
% 0.21/0.51  % (5828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5830)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (5831)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (5827)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (5827)Refutation not found, incomplete strategy% (5827)------------------------------
% 0.21/0.53  % (5827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5827)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5827)Memory used [KB]: 6268
% 0.21/0.53  % (5827)Time elapsed: 0.108 s
% 0.21/0.53  % (5827)------------------------------
% 0.21/0.53  % (5827)------------------------------
% 1.30/0.53  % (5828)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (5828)Memory used [KB]: 10746
% 1.30/0.53  % (5828)Time elapsed: 0.085 s
% 1.30/0.53  % (5828)------------------------------
% 1.30/0.53  % (5828)------------------------------
% 1.30/0.53  % (5846)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.30/0.53  % (5825)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.30/0.53  % (5843)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.30/0.53  % (5822)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.53  % (5825)Refutation not found, incomplete strategy% (5825)------------------------------
% 1.30/0.53  % (5825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (5825)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (5825)Memory used [KB]: 6268
% 1.30/0.53  % (5825)Time elapsed: 0.091 s
% 1.30/0.53  % (5825)------------------------------
% 1.30/0.53  % (5825)------------------------------
% 1.30/0.53  % (5843)Refutation not found, incomplete strategy% (5843)------------------------------
% 1.30/0.53  % (5843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (5843)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (5843)Memory used [KB]: 1791
% 1.30/0.53  % (5843)Time elapsed: 0.109 s
% 1.30/0.53  % (5843)------------------------------
% 1.30/0.53  % (5843)------------------------------
% 1.30/0.53  % (5820)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.53  % (5823)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.30/0.53  % (5820)Refutation not found, incomplete strategy% (5820)------------------------------
% 1.30/0.53  % (5820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (5820)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (5820)Memory used [KB]: 1663
% 1.30/0.53  % (5820)Time elapsed: 0.116 s
% 1.30/0.53  % (5820)------------------------------
% 1.30/0.53  % (5820)------------------------------
% 1.30/0.53  % (5849)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.30/0.53  % (5822)Refutation not found, incomplete strategy% (5822)------------------------------
% 1.30/0.53  % (5822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (5830)Refutation not found, incomplete strategy% (5830)------------------------------
% 1.30/0.54  % (5830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (5830)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (5830)Memory used [KB]: 10618
% 1.30/0.54  % (5830)Time elapsed: 0.125 s
% 1.30/0.54  % (5830)------------------------------
% 1.30/0.54  % (5830)------------------------------
% 1.30/0.54  % (5835)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.30/0.54  % (5835)Refutation not found, incomplete strategy% (5835)------------------------------
% 1.30/0.54  % (5835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (5835)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (5835)Memory used [KB]: 6140
% 1.30/0.54  % (5835)Time elapsed: 0.002 s
% 1.30/0.54  % (5835)------------------------------
% 1.30/0.54  % (5835)------------------------------
% 1.30/0.54  % (5824)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.30/0.54  % (5831)Refutation not found, incomplete strategy% (5831)------------------------------
% 1.30/0.54  % (5831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (5831)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (5831)Memory used [KB]: 10618
% 1.30/0.54  % (5831)Time elapsed: 0.126 s
% 1.30/0.54  % (5831)------------------------------
% 1.30/0.54  % (5831)------------------------------
% 1.30/0.54  % (5842)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.30/0.54  % (5842)Refutation not found, incomplete strategy% (5842)------------------------------
% 1.30/0.54  % (5842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (5842)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (5842)Memory used [KB]: 10746
% 1.30/0.54  % (5842)Time elapsed: 0.127 s
% 1.30/0.54  % (5842)------------------------------
% 1.30/0.54  % (5842)------------------------------
% 1.30/0.54  % (5841)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.30/0.54  % (5838)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.30/0.54  % (5834)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.30/0.54  % (5841)Refutation not found, incomplete strategy% (5841)------------------------------
% 1.30/0.54  % (5841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (5841)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (5841)Memory used [KB]: 1791
% 1.30/0.54  % (5841)Time elapsed: 0.095 s
% 1.30/0.54  % (5841)------------------------------
% 1.30/0.54  % (5841)------------------------------
% 1.30/0.54  % (5847)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.30/0.54  % (5833)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.30/0.54  % (5822)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (5822)Memory used [KB]: 10746
% 1.30/0.54  % (5822)Time elapsed: 0.119 s
% 1.30/0.54  % (5822)------------------------------
% 1.30/0.54  % (5822)------------------------------
% 1.50/0.55  % (5839)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.55  % (5826)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.50/0.55  % SZS status CounterSatisfiable for theBenchmark
% 1.50/0.55  % (5826)# SZS output start Saturation.
% 1.50/0.55  cnf(u23,negated_conjecture,
% 1.50/0.55      l1_struct_0(sK0)).
% 1.50/0.55  
% 1.50/0.55  cnf(u28,axiom,
% 1.50/0.55      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 1.50/0.55  
% 1.50/0.55  cnf(u43,axiom,
% 1.50/0.55      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.50/0.55  
% 1.50/0.55  cnf(u22,negated_conjecture,
% 1.50/0.55      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.50/0.55  
% 1.50/0.55  cnf(u86,negated_conjecture,
% 1.50/0.55      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 1.50/0.55  
% 1.50/0.55  % (5846)Refutation not found, incomplete strategy% (5846)------------------------------
% 1.50/0.55  % (5846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  cnf(u59,axiom,
% 1.50/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 1.50/0.55  
% 1.50/0.55  cnf(u24,axiom,
% 1.50/0.55      r1_tarski(k1_xboole_0,X0)).
% 1.50/0.55  
% 1.50/0.55  % (5846)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  cnf(u40,axiom,
% 1.50/0.55      ~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0).
% 1.50/0.55  
% 1.50/0.55  % (5846)Memory used [KB]: 10874
% 1.50/0.55  cnf(u44,axiom,
% 1.50/0.55      k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))).
% 1.50/0.55  
% 1.50/0.55  % (5846)Time elapsed: 0.146 s
% 1.50/0.55  cnf(u89,negated_conjecture,
% 1.50/0.55      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 1.50/0.55  
% 1.50/0.55  % (5846)------------------------------
% 1.50/0.55  % (5846)------------------------------
% 1.50/0.55  cnf(u87,negated_conjecture,
% 1.50/0.55      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 1.50/0.55  
% 1.50/0.55  cnf(u88,negated_conjecture,
% 1.50/0.55      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 1.50/0.55  
% 1.50/0.55  cnf(u61,negated_conjecture,
% 1.50/0.55      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 1.50/0.55  
% 1.50/0.55  cnf(u65,axiom,
% 1.50/0.55      k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1)).
% 1.50/0.55  
% 1.50/0.55  cnf(u71,axiom,
% 1.50/0.55      k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2)))).
% 1.50/0.55  
% 1.50/0.55  cnf(u64,axiom,
% 1.50/0.55      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 1.50/0.55  
% 1.50/0.55  cnf(u20,negated_conjecture,
% 1.50/0.55      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 1.50/0.55  
% 1.50/0.55  cnf(u58,axiom,
% 1.50/0.55      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 1.50/0.55  
% 1.50/0.55  cnf(u60,axiom,
% 1.50/0.55      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))))).
% 1.50/0.55  
% 1.50/0.55  cnf(u51,axiom,
% 1.50/0.55      k1_xboole_0 = k5_xboole_0(X1,X1)).
% 1.50/0.55  
% 1.50/0.55  cnf(u38,axiom,
% 1.50/0.55      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 1.50/0.55  
% 1.50/0.55  cnf(u26,axiom,
% 1.50/0.55      k5_xboole_0(X0,k1_xboole_0) = X0).
% 1.50/0.55  
% 1.50/0.55  cnf(u25,axiom,
% 1.50/0.55      k2_subset_1(X0) = X0).
% 1.50/0.55  
% 1.50/0.55  cnf(u42,negated_conjecture,
% 1.50/0.55      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.50/0.55  
% 1.50/0.55  % (5826)# SZS output end Saturation.
% 1.50/0.55  % (5826)------------------------------
% 1.50/0.55  % (5826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (5826)Termination reason: Satisfiable
% 1.50/0.55  
% 1.50/0.55  % (5826)Memory used [KB]: 6268
% 1.50/0.55  % (5826)Time elapsed: 0.141 s
% 1.50/0.55  % (5826)------------------------------
% 1.50/0.55  % (5826)------------------------------
% 1.50/0.55  % (5839)Refutation not found, incomplete strategy% (5839)------------------------------
% 1.50/0.55  % (5839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (5839)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (5839)Memory used [KB]: 10746
% 1.50/0.55  % (5839)Time elapsed: 0.145 s
% 1.50/0.55  % (5839)------------------------------
% 1.50/0.55  % (5839)------------------------------
% 1.50/0.55  % (5819)Success in time 0.186 s
%------------------------------------------------------------------------------
