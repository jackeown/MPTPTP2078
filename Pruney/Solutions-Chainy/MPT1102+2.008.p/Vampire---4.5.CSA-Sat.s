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
% DateTime   : Thu Dec  3 13:08:29 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    0
%              Number of atoms          :   24 (  24 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u18,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u28,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) )).

cnf(u32,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u27,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u29,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u34,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u33,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u31,axiom,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 )).

cnf(u40,axiom,
    ( ~ r1_tarski(X3,X2)
    | k7_subset_1(X2,X3,X4) = k4_xboole_0(X3,X4) )).

cnf(u37,negated_conjecture,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) )).

cnf(u38,axiom,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) )).

cnf(u36,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u21,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u23,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u39,axiom,
    ( k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u41,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X5) = k4_xboole_0(sK1,X5) )).

cnf(u30,axiom,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) )).

cnf(u20,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:24:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.40  % (26489)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.42  % (26498)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.45  % (26491)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.45  % (26485)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (26499)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (26483)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (26484)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (26487)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (26486)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (26490)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (26488)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.47  % (26484)# SZS output start Saturation.
% 0.20/0.47  cnf(u18,negated_conjecture,
% 0.20/0.47      l1_struct_0(sK0)).
% 0.20/0.47  
% 0.20/0.47  cnf(u19,negated_conjecture,
% 0.20/0.47      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.47  
% 0.20/0.47  cnf(u28,axiom,
% 0.20/0.47      m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)).
% 0.20/0.47  
% 0.20/0.47  cnf(u32,axiom,
% 0.20/0.47      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.20/0.47  
% 0.20/0.47  cnf(u27,axiom,
% 0.20/0.47      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.20/0.47  
% 0.20/0.47  cnf(u29,axiom,
% 0.20/0.47      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.20/0.47  
% 0.20/0.47  cnf(u34,negated_conjecture,
% 0.20/0.47      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.20/0.47  
% 0.20/0.47  cnf(u33,axiom,
% 0.20/0.47      r1_tarski(X0,X0)).
% 0.20/0.47  
% 0.20/0.47  cnf(u31,axiom,
% 0.20/0.47      ~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0).
% 0.20/0.47  
% 0.20/0.47  cnf(u40,axiom,
% 0.20/0.47      ~r1_tarski(X3,X2) | k7_subset_1(X2,X3,X4) = k4_xboole_0(X3,X4)).
% 0.20/0.47  
% 0.20/0.47  cnf(u37,negated_conjecture,
% 0.20/0.47      sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))).
% 0.20/0.47  
% 0.20/0.47  cnf(u38,axiom,
% 0.20/0.47      k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))).
% 0.20/0.47  
% 0.20/0.47  cnf(u36,axiom,
% 0.20/0.47      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 0.20/0.47  
% 0.20/0.47  cnf(u21,axiom,
% 0.20/0.47      k2_subset_1(X0) = X0).
% 0.20/0.47  
% 0.20/0.47  cnf(u23,axiom,
% 0.20/0.47      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 0.20/0.47  
% 0.20/0.47  cnf(u39,axiom,
% 0.20/0.47      k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)).
% 0.20/0.47  
% 0.20/0.47  cnf(u41,negated_conjecture,
% 0.20/0.47      k7_subset_1(u1_struct_0(sK0),sK1,X5) = k4_xboole_0(sK1,X5)).
% 0.20/0.47  
% 0.20/0.47  cnf(u30,axiom,
% 0.20/0.47      k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))).
% 0.20/0.47  
% 0.20/0.47  cnf(u20,negated_conjecture,
% 0.20/0.47      sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.20/0.47  
% 0.20/0.47  % (26484)# SZS output end Saturation.
% 0.20/0.47  % (26484)------------------------------
% 0.20/0.47  % (26484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (26484)Termination reason: Satisfiable
% 0.20/0.47  
% 0.20/0.47  % (26484)Memory used [KB]: 1663
% 0.20/0.47  % (26484)Time elapsed: 0.072 s
% 0.20/0.47  % (26484)------------------------------
% 0.20/0.47  % (26484)------------------------------
% 0.20/0.47  % (26493)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (26479)Success in time 0.123 s
%------------------------------------------------------------------------------
