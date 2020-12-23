%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:03 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   23 (  23 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    0
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u21,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u36,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK2,X0) = k2_xboole_0(sK2,X0) )).

cnf(u37,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,X1) = k2_xboole_0(sK1,X1) )).

cnf(u23,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) )).

cnf(u24,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u25,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u26,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) )).

cnf(u19,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u22,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 )).

cnf(u32,negated_conjecture,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u43,negated_conjecture,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u33,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u42,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

cnf(u18,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u35,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X1) = k4_xboole_0(sK1,X1) )).

cnf(u34,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) )).

cnf(u41,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) )).

cnf(u39,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1) )).

cnf(u38,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) )).

cnf(u29,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u28,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) )).

cnf(u20,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:46:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (3605)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.48  % (3601)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (3597)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.48  % (3605)Refutation not found, incomplete strategy% (3605)------------------------------
% 0.22/0.48  % (3605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (3597)Refutation not found, incomplete strategy% (3597)------------------------------
% 0.22/0.48  % (3597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (3605)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (3605)Memory used [KB]: 6140
% 0.22/0.48  % (3605)Time elapsed: 0.072 s
% 0.22/0.48  % (3605)------------------------------
% 0.22/0.48  % (3605)------------------------------
% 0.22/0.48  % (3593)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (3601)Refutation not found, incomplete strategy% (3601)------------------------------
% 0.22/0.48  % (3601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (3601)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (3601)Memory used [KB]: 6140
% 0.22/0.48  % (3601)Time elapsed: 0.008 s
% 0.22/0.48  % (3601)------------------------------
% 0.22/0.48  % (3601)------------------------------
% 0.22/0.48  % (3587)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (3597)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (3597)Memory used [KB]: 10618
% 0.22/0.48  % (3597)Time elapsed: 0.073 s
% 0.22/0.48  % (3597)------------------------------
% 0.22/0.48  % (3597)------------------------------
% 0.22/0.49  % (3594)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (3599)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (3599)Refutation not found, incomplete strategy% (3599)------------------------------
% 0.22/0.49  % (3599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (3599)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (3599)Memory used [KB]: 1663
% 0.22/0.49  % (3599)Time elapsed: 0.077 s
% 0.22/0.49  % (3599)------------------------------
% 0.22/0.49  % (3599)------------------------------
% 0.22/0.49  % (3592)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (3590)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (3592)Refutation not found, incomplete strategy% (3592)------------------------------
% 0.22/0.50  % (3592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (3592)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (3592)Memory used [KB]: 10618
% 0.22/0.50  % (3592)Time elapsed: 0.080 s
% 0.22/0.50  % (3592)------------------------------
% 0.22/0.50  % (3592)------------------------------
% 0.22/0.50  % (3591)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (3586)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (3596)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (3586)Refutation not found, incomplete strategy% (3586)------------------------------
% 0.22/0.50  % (3586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (3586)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (3586)Memory used [KB]: 10618
% 0.22/0.50  % (3586)Time elapsed: 0.081 s
% 0.22/0.50  % (3586)------------------------------
% 0.22/0.50  % (3586)------------------------------
% 0.22/0.50  % (3596)Refutation not found, incomplete strategy% (3596)------------------------------
% 0.22/0.50  % (3596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (3596)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (3596)Memory used [KB]: 6140
% 0.22/0.50  % (3596)Time elapsed: 0.086 s
% 0.22/0.50  % (3596)------------------------------
% 0.22/0.50  % (3596)------------------------------
% 0.22/0.50  % (3600)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (3587)Refutation not found, incomplete strategy% (3587)------------------------------
% 0.22/0.50  % (3587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (3587)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (3587)Memory used [KB]: 10618
% 0.22/0.50  % (3587)Time elapsed: 0.064 s
% 0.22/0.50  % (3587)------------------------------
% 0.22/0.50  % (3587)------------------------------
% 0.22/0.50  % (3598)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (3603)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % (3598)Refutation not found, incomplete strategy% (3598)------------------------------
% 0.22/0.50  % (3598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (3598)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (3598)Memory used [KB]: 6012
% 0.22/0.50  % (3598)Time elapsed: 0.001 s
% 0.22/0.50  % (3598)------------------------------
% 0.22/0.50  % (3598)------------------------------
% 0.22/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.50  % (3603)# SZS output start Saturation.
% 0.22/0.50  cnf(u21,negated_conjecture,
% 0.22/0.50      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.50  
% 0.22/0.50  cnf(u17,negated_conjecture,
% 0.22/0.50      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.50  
% 0.22/0.50  cnf(u36,negated_conjecture,
% 0.22/0.50      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK2,X0) = k2_xboole_0(sK2,X0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u37,negated_conjecture,
% 0.22/0.50      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X1) = k2_xboole_0(sK1,X1)).
% 0.22/0.50  
% 0.22/0.50  cnf(u23,axiom,
% 0.22/0.50      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)).
% 0.22/0.50  
% 0.22/0.50  cnf(u24,axiom,
% 0.22/0.50      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.22/0.50  
% 0.22/0.50  cnf(u25,axiom,
% 0.22/0.50      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.22/0.50  
% 0.22/0.50  cnf(u26,axiom,
% 0.22/0.50      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)).
% 0.22/0.50  
% 0.22/0.50  cnf(u19,negated_conjecture,
% 0.22/0.50      r1_xboole_0(sK1,sK2)).
% 0.22/0.50  
% 0.22/0.50  cnf(u22,axiom,
% 0.22/0.50      ~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0).
% 0.22/0.50  
% 0.22/0.51  cnf(u32,negated_conjecture,
% 0.22/0.51      sK2 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.22/0.51  
% 0.22/0.51  cnf(u43,negated_conjecture,
% 0.22/0.51      sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u33,negated_conjecture,
% 0.22/0.51      sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u42,negated_conjecture,
% 0.22/0.51      k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u18,negated_conjecture,
% 0.22/0.51      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u35,negated_conjecture,
% 0.22/0.51      k7_subset_1(u1_struct_0(sK0),sK1,X1) = k4_xboole_0(sK1,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u34,negated_conjecture,
% 0.22/0.51      k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u41,negated_conjecture,
% 0.22/0.51      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u39,negated_conjecture,
% 0.22/0.51      k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u38,negated_conjecture,
% 0.22/0.51      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u29,negated_conjecture,
% 0.22/0.51      k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u28,negated_conjecture,
% 0.22/0.51      k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u20,negated_conjecture,
% 0.22/0.51      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.22/0.51  
% 0.22/0.51  % (3603)# SZS output end Saturation.
% 0.22/0.51  % (3603)------------------------------
% 0.22/0.51  % (3603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3603)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (3603)Memory used [KB]: 1663
% 0.22/0.51  % (3603)Time elapsed: 0.096 s
% 0.22/0.51  % (3603)------------------------------
% 0.22/0.51  % (3603)------------------------------
% 0.22/0.51  % (3590)Refutation not found, incomplete strategy% (3590)------------------------------
% 0.22/0.51  % (3590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3590)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3590)Memory used [KB]: 1663
% 0.22/0.51  % (3590)Time elapsed: 0.092 s
% 0.22/0.51  % (3590)------------------------------
% 0.22/0.51  % (3590)------------------------------
% 0.22/0.51  % (3582)Success in time 0.142 s
%------------------------------------------------------------------------------
