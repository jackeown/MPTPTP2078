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
% DateTime   : Thu Dec  3 13:08:42 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of clauses        :   20 (  20 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    0
%              Number of atoms          :   35 (  35 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u16,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u26,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) )).

cnf(u17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u25,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u29,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u32,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u30,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u39,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | u1_struct_0(sK0) = sK1 )).

cnf(u40,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
    | k2_struct_0(sK0) != sK1 )).

cnf(u36,axiom,
    ( ~ r1_tarski(k1_xboole_0,k4_xboole_0(X0,X1))
    | ~ r1_tarski(k4_xboole_0(X0,X1),k1_xboole_0)
    | r1_tarski(X0,X1) )).

cnf(u28,axiom,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u24,axiom,
    ( ~ r1_tarski(X1,X0)
    | X0 = X1
    | ~ r1_tarski(X0,X1) )).

cnf(u48,axiom,
    ( ~ r1_tarski(X2,X1)
    | k4_xboole_0(X2,X3) = k7_subset_1(X1,X2,X3) )).

cnf(u49,axiom,
    ( k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u47,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u21,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) = sK1 )).

cnf(u35,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u34,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u18,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) != sK1 )).

cnf(u27,axiom,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:54:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.19/0.49  % (22457)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.49  % (22458)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.49  % (22457)Refutation not found, incomplete strategy% (22457)------------------------------
% 0.19/0.49  % (22457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (22457)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (22457)Memory used [KB]: 1663
% 0.19/0.49  % (22457)Time elapsed: 0.082 s
% 0.19/0.49  % (22457)------------------------------
% 0.19/0.49  % (22457)------------------------------
% 0.19/0.49  % (22458)Refutation not found, incomplete strategy% (22458)------------------------------
% 0.19/0.49  % (22458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (22458)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (22458)Memory used [KB]: 1663
% 0.19/0.49  % (22458)Time elapsed: 0.089 s
% 0.19/0.49  % (22458)------------------------------
% 0.19/0.49  % (22458)------------------------------
% 0.19/0.49  % (22466)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.49  % (22470)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.19/0.50  % (22466)# SZS output start Saturation.
% 0.19/0.50  cnf(u16,negated_conjecture,
% 0.19/0.50      l1_struct_0(sK0)).
% 0.19/0.50  
% 0.19/0.50  cnf(u26,axiom,
% 0.19/0.50      m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)).
% 0.19/0.50  
% 0.19/0.50  cnf(u17,negated_conjecture,
% 0.19/0.50      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.19/0.50  
% 0.19/0.50  cnf(u25,axiom,
% 0.19/0.50      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.19/0.50  
% 0.19/0.50  cnf(u29,axiom,
% 0.19/0.50      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.19/0.50  
% 0.19/0.50  cnf(u32,negated_conjecture,
% 0.19/0.50      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.19/0.50  
% 0.19/0.50  cnf(u30,axiom,
% 0.19/0.50      r1_tarski(X1,X1)).
% 0.19/0.50  
% 0.19/0.50  cnf(u39,negated_conjecture,
% 0.19/0.50      ~r1_tarski(u1_struct_0(sK0),sK1) | u1_struct_0(sK0) = sK1).
% 0.19/0.50  
% 0.19/0.50  cnf(u40,negated_conjecture,
% 0.19/0.50      ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) | k2_struct_0(sK0) != sK1).
% 0.19/0.50  
% 0.19/0.50  cnf(u36,axiom,
% 0.19/0.50      ~r1_tarski(k1_xboole_0,k4_xboole_0(X0,X1)) | ~r1_tarski(k4_xboole_0(X0,X1),k1_xboole_0) | r1_tarski(X0,X1)).
% 0.19/0.50  
% 0.19/0.50  cnf(u28,axiom,
% 0.19/0.50      ~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0).
% 0.19/0.50  
% 0.19/0.50  cnf(u24,axiom,
% 0.19/0.50      ~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)).
% 0.19/0.50  
% 0.19/0.50  cnf(u48,axiom,
% 0.19/0.50      ~r1_tarski(X2,X1) | k4_xboole_0(X2,X3) = k7_subset_1(X1,X2,X3)).
% 0.19/0.50  
% 0.19/0.50  cnf(u49,axiom,
% 0.19/0.50      k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)).
% 0.19/0.50  
% 0.19/0.50  cnf(u47,negated_conjecture,
% 0.19/0.50      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 0.19/0.50  
% 0.19/0.50  cnf(u21,negated_conjecture,
% 0.19/0.50      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) = sK1).
% 0.19/0.50  
% 0.19/0.50  cnf(u35,negated_conjecture,
% 0.19/0.50      k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))).
% 0.19/0.50  
% 0.19/0.50  cnf(u34,axiom,
% 0.19/0.50      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 0.19/0.50  
% 0.19/0.50  cnf(u18,negated_conjecture,
% 0.19/0.50      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) != sK1).
% 0.19/0.50  
% 0.19/0.50  cnf(u27,axiom,
% 0.19/0.50      k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)).
% 0.19/0.50  
% 0.19/0.50  % (22466)# SZS output end Saturation.
% 0.19/0.50  % (22466)------------------------------
% 0.19/0.50  % (22466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (22466)Termination reason: Satisfiable
% 0.19/0.50  
% 0.19/0.50  % (22466)Memory used [KB]: 1663
% 0.19/0.50  % (22466)Time elapsed: 0.102 s
% 0.19/0.50  % (22466)------------------------------
% 0.19/0.50  % (22466)------------------------------
% 0.19/0.50  % (22456)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.50  % (22474)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.50  % (22449)Success in time 0.146 s
%------------------------------------------------------------------------------
