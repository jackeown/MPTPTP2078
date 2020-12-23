%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:41 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   18 (  18 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    0
%              Number of atoms          :   29 (  29 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

cnf(u41,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | u1_struct_0(sK0) = sK1 )).

cnf(u28,axiom,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u24,axiom,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 )).

cnf(u43,axiom,
    ( ~ r1_tarski(X2,X1)
    | k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) )).

cnf(u44,axiom,
    ( k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u42,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u21,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) = sK1 )).

cnf(u35,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u34,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u18,negated_conjecture,
    ( k2_struct_0(sK0) != sK1
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

cnf(u27,axiom,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:03:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (11062)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (11062)Refutation not found, incomplete strategy% (11062)------------------------------
% 0.20/0.47  % (11062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (11070)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.48  % (11062)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (11062)Memory used [KB]: 6140
% 0.20/0.48  % (11062)Time elapsed: 0.052 s
% 0.20/0.48  % (11062)------------------------------
% 0.20/0.48  % (11062)------------------------------
% 0.20/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.48  % (11070)# SZS output start Saturation.
% 0.20/0.48  cnf(u16,negated_conjecture,
% 0.20/0.48      l1_struct_0(sK0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u26,axiom,
% 0.20/0.48      m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)).
% 0.20/0.48  
% 0.20/0.48  cnf(u17,negated_conjecture,
% 0.20/0.48      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.48  
% 0.20/0.48  cnf(u25,axiom,
% 0.20/0.48      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.20/0.48  
% 0.20/0.48  cnf(u29,axiom,
% 0.20/0.48      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.20/0.48  
% 0.20/0.48  cnf(u32,negated_conjecture,
% 0.20/0.48      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.20/0.48  
% 0.20/0.48  cnf(u30,axiom,
% 0.20/0.48      r1_tarski(X1,X1)).
% 0.20/0.48  
% 0.20/0.48  cnf(u41,negated_conjecture,
% 0.20/0.48      ~r1_tarski(u1_struct_0(sK0),sK1) | u1_struct_0(sK0) = sK1).
% 0.20/0.48  
% 0.20/0.48  cnf(u28,axiom,
% 0.20/0.48      ~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0).
% 0.20/0.48  
% 0.20/0.48  cnf(u24,axiom,
% 0.20/0.48      ~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1).
% 0.20/0.48  
% 0.20/0.48  cnf(u43,axiom,
% 0.20/0.48      ~r1_tarski(X2,X1) | k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3)).
% 0.20/0.48  
% 0.20/0.48  cnf(u44,axiom,
% 0.20/0.48      k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)).
% 0.20/0.48  
% 0.20/0.48  cnf(u42,negated_conjecture,
% 0.20/0.48      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u21,negated_conjecture,
% 0.20/0.48      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) = sK1).
% 0.20/0.48  
% 0.20/0.48  cnf(u35,negated_conjecture,
% 0.20/0.48      k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))).
% 0.20/0.48  
% 0.20/0.48  cnf(u34,axiom,
% 0.20/0.48      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u18,negated_conjecture,
% 0.20/0.48      k2_struct_0(sK0) != sK1 | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.20/0.48  
% 0.20/0.48  cnf(u27,axiom,
% 0.20/0.48      k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)).
% 0.20/0.48  
% 0.20/0.48  % (11070)# SZS output end Saturation.
% 0.20/0.48  % (11070)------------------------------
% 0.20/0.48  % (11070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (11070)Termination reason: Satisfiable
% 0.20/0.48  
% 0.20/0.48  % (11070)Memory used [KB]: 6140
% 0.20/0.48  % (11070)Time elapsed: 0.062 s
% 0.20/0.48  % (11070)------------------------------
% 0.20/0.48  % (11070)------------------------------
% 0.20/0.49  % (11048)Success in time 0.123 s
%------------------------------------------------------------------------------
