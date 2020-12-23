%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:31 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   23 (  23 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    0
%              Number of atoms          :   32 (  32 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u18,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u27,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) )).

cnf(u32,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u26,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u30,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u34,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u28,axiom,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 )).

cnf(u33,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u29,axiom,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u61,axiom,
    ( ~ r1_tarski(X3,X2)
    | k7_subset_1(X2,X3,X4) = k4_xboole_0(X3,X4) )).

cnf(u60,axiom,
    ( k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u62,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X5) = k4_xboole_0(sK1,X5) )).

cnf(u64,axiom,
    ( k7_subset_1(X2,X3,X4) = k4_xboole_0(X3,X4)
    | k1_xboole_0 != k4_xboole_0(X3,X2) )).

cnf(u31,axiom,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) )).

cnf(u41,axiom,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) )).

cnf(u36,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u38,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u22,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u21,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u66,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(k2_struct_0(sK0),u1_struct_0(sK0))
    | sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) )).

cnf(u67,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(k2_struct_0(sK0),u1_struct_0(sK0))
    | sK1 != k4_xboole_0(k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u20,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (7427)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.45  % (7436)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (7425)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (7426)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (7424)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.46  % (7425)# SZS output start Saturation.
% 0.20/0.46  cnf(u18,negated_conjecture,
% 0.20/0.46      l1_struct_0(sK0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u19,negated_conjecture,
% 0.20/0.46      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.46  
% 0.20/0.46  cnf(u27,axiom,
% 0.20/0.46      m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)).
% 0.20/0.46  
% 0.20/0.46  cnf(u32,axiom,
% 0.20/0.46      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.20/0.46  
% 0.20/0.46  cnf(u26,axiom,
% 0.20/0.46      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.20/0.46  
% 0.20/0.46  cnf(u30,axiom,
% 0.20/0.46      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.20/0.46  
% 0.20/0.46  cnf(u34,negated_conjecture,
% 0.20/0.46      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.20/0.46  
% 0.20/0.46  cnf(u28,axiom,
% 0.20/0.46      r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0).
% 0.20/0.46  
% 0.20/0.46  cnf(u33,axiom,
% 0.20/0.46      r1_tarski(X0,X0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u29,axiom,
% 0.20/0.46      ~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0).
% 0.20/0.46  
% 0.20/0.46  cnf(u61,axiom,
% 0.20/0.46      ~r1_tarski(X3,X2) | k7_subset_1(X2,X3,X4) = k4_xboole_0(X3,X4)).
% 0.20/0.46  
% 0.20/0.46  cnf(u60,axiom,
% 0.20/0.46      k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)).
% 0.20/0.46  
% 0.20/0.46  cnf(u62,negated_conjecture,
% 0.20/0.46      k7_subset_1(u1_struct_0(sK0),sK1,X5) = k4_xboole_0(sK1,X5)).
% 0.20/0.46  
% 0.20/0.46  cnf(u64,axiom,
% 0.20/0.46      k7_subset_1(X2,X3,X4) = k4_xboole_0(X3,X4) | k1_xboole_0 != k4_xboole_0(X3,X2)).
% 0.20/0.46  
% 0.20/0.46  cnf(u31,axiom,
% 0.20/0.46      k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))).
% 0.20/0.46  
% 0.20/0.46  cnf(u41,axiom,
% 0.20/0.46      k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))).
% 0.20/0.46  
% 0.20/0.46  cnf(u36,axiom,
% 0.20/0.46      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u38,negated_conjecture,
% 0.20/0.46      k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))).
% 0.20/0.46  
% 0.20/0.46  cnf(u22,axiom,
% 0.20/0.46      k4_xboole_0(X0,k1_xboole_0) = X0).
% 0.20/0.46  
% 0.20/0.46  cnf(u21,axiom,
% 0.20/0.46      k2_subset_1(X0) = X0).
% 0.20/0.46  
% 0.20/0.46  cnf(u66,negated_conjecture,
% 0.20/0.46      k1_xboole_0 != k4_xboole_0(k2_struct_0(sK0),u1_struct_0(sK0)) | sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))).
% 0.20/0.46  
% 0.20/0.46  cnf(u67,negated_conjecture,
% 0.20/0.46      k1_xboole_0 != k4_xboole_0(k2_struct_0(sK0),u1_struct_0(sK0)) | sK1 != k4_xboole_0(k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.20/0.46  
% 0.20/0.46  cnf(u20,negated_conjecture,
% 0.20/0.46      sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.20/0.46  
% 0.20/0.46  % (7425)# SZS output end Saturation.
% 0.20/0.46  % (7425)------------------------------
% 0.20/0.46  % (7425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (7425)Termination reason: Satisfiable
% 0.20/0.46  
% 0.20/0.46  % (7425)Memory used [KB]: 1663
% 0.20/0.46  % (7425)Time elapsed: 0.053 s
% 0.20/0.46  % (7425)------------------------------
% 0.20/0.46  % (7425)------------------------------
% 0.20/0.46  % (7437)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (7423)Success in time 0.113 s
%------------------------------------------------------------------------------
