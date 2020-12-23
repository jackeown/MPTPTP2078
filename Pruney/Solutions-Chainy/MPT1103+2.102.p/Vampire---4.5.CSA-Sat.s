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
% DateTime   : Thu Dec  3 13:08:47 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   24 (  24 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    0
%              Number of atoms          :   36 (  36 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u16,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u35,axiom,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) )).

cnf(u15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u26,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u20,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0)
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u22,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u25,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u28,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u27,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u21,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u23,axiom,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u30,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u38,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u34,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2) )).

cnf(u41,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u37,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u44,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u13,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u33,axiom,
    ( k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u18,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u17,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u29,axiom,
    ( k1_xboole_0 != X0
    | r1_tarski(X0,k1_xboole_0) )).

cnf(u14,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 != k2_struct_0(sK0) )).

cnf(u24,axiom,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:54:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (20480)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (20485)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (20489)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (20480)Refutation not found, incomplete strategy% (20480)------------------------------
% 0.20/0.47  % (20480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (20493)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (20496)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.48  % (20485)Refutation not found, incomplete strategy% (20485)------------------------------
% 0.20/0.48  % (20485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (20485)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (20485)Memory used [KB]: 10618
% 0.20/0.48  % (20485)Time elapsed: 0.059 s
% 0.20/0.48  % (20485)------------------------------
% 0.20/0.48  % (20485)------------------------------
% 0.20/0.48  % (20489)Refutation not found, incomplete strategy% (20489)------------------------------
% 0.20/0.48  % (20489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.48  % (20489)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (20489)Memory used [KB]: 6140
% 0.20/0.48  % (20489)Time elapsed: 0.074 s
% 0.20/0.48  % (20489)------------------------------
% 0.20/0.48  % (20489)------------------------------
% 0.20/0.48  % (20488)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (20480)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (20480)Memory used [KB]: 10618
% 0.20/0.48  % (20480)Time elapsed: 0.065 s
% 0.20/0.48  % (20480)------------------------------
% 0.20/0.48  % (20480)------------------------------
% 0.20/0.48  % (20496)# SZS output start Saturation.
% 0.20/0.48  cnf(u16,negated_conjecture,
% 0.20/0.48      l1_struct_0(sK0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u35,axiom,
% 0.20/0.48      ~l1_struct_0(X0) | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)))).
% 0.20/0.48  
% 0.20/0.48  cnf(u15,negated_conjecture,
% 0.20/0.48      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.48  
% 0.20/0.48  cnf(u26,axiom,
% 0.20/0.48      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.20/0.48  
% 0.20/0.48  cnf(u20,axiom,
% 0.20/0.48      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.20/0.48  
% 0.20/0.48  cnf(u22,axiom,
% 0.20/0.48      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.20/0.48  
% 0.20/0.48  cnf(u25,axiom,
% 0.20/0.48      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.20/0.48  
% 0.20/0.48  cnf(u28,negated_conjecture,
% 0.20/0.48      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.20/0.48  
% 0.20/0.48  cnf(u27,axiom,
% 0.20/0.48      r1_tarski(X0,X0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u21,axiom,
% 0.20/0.48      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 0.20/0.48  
% 0.20/0.48  cnf(u23,axiom,
% 0.20/0.48      ~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0).
% 0.20/0.48  
% 0.20/0.48  cnf(u30,axiom,
% 0.20/0.48      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u38,negated_conjecture,
% 0.20/0.48      k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))).
% 0.20/0.48  
% 0.20/0.48  cnf(u34,negated_conjecture,
% 0.20/0.48      k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2)).
% 0.20/0.48  
% 0.20/0.48  cnf(u41,negated_conjecture,
% 0.20/0.48      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u37,negated_conjecture,
% 0.20/0.48      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.20/0.48  
% 0.20/0.48  cnf(u44,negated_conjecture,
% 0.20/0.48      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.48  
% 0.20/0.48  cnf(u13,negated_conjecture,
% 0.20/0.48      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u33,axiom,
% 0.20/0.48      k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)).
% 0.20/0.48  
% 0.20/0.48  cnf(u18,axiom,
% 0.20/0.48      k4_xboole_0(X0,k1_xboole_0) = X0).
% 0.20/0.48  
% 0.20/0.48  cnf(u17,axiom,
% 0.20/0.48      k2_subset_1(X0) = X0).
% 0.20/0.48  
% 0.20/0.48  cnf(u29,axiom,
% 0.20/0.48      k1_xboole_0 != X0 | r1_tarski(X0,k1_xboole_0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u14,negated_conjecture,
% 0.20/0.48      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 != k2_struct_0(sK0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u24,axiom,
% 0.20/0.48      k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)).
% 0.20/0.48  
% 0.20/0.48  % (20496)# SZS output end Saturation.
% 0.20/0.48  % (20496)------------------------------
% 0.20/0.48  % (20496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (20496)Termination reason: Satisfiable
% 0.20/0.48  
% 0.20/0.48  % (20496)Memory used [KB]: 1663
% 0.20/0.48  % (20496)Time elapsed: 0.072 s
% 0.20/0.48  % (20496)------------------------------
% 0.20/0.48  % (20496)------------------------------
% 0.20/0.49  % (20478)Success in time 0.124 s
%------------------------------------------------------------------------------
