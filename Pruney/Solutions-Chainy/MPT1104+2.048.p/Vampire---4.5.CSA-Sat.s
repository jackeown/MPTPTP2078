%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:56 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   49 (  49 expanded)
%              Number of leaves         :   49 (  49 expanded)
%              Depth                    :    0
%              Number of atoms          :   56 (  56 expanded)
%              Number of equality atoms :   45 (  45 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u46,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u27,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u87,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k3_tarski(k2_tarski(X0,sK2)) )).

cnf(u88,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k3_tarski(k2_tarski(X1,sK1)) )).

cnf(u63,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u45,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) )).

cnf(u89,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | k3_tarski(k2_tarski(X2,X3)) = k4_subset_1(X3,X2,X3) )).

cnf(u25,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u67,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k3_tarski(k2_tarski(k7_subset_1(X2,X2,X0),X1)) = k7_subset_1(k3_tarski(k2_tarski(X2,X1)),k3_tarski(k2_tarski(X2,X1)),X0) )).

cnf(u140,negated_conjecture,
    ( sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) )).

cnf(u136,negated_conjecture,
    ( sK2 = k7_subset_1(sK2,sK2,sK1) )).

cnf(u66,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) )).

cnf(u65,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1) )).

cnf(u138,negated_conjecture,
    ( k4_subset_1(sK2,sK2,sK2) = k7_subset_1(k4_subset_1(sK2,sK2,sK2),k4_subset_1(sK2,sK2,sK2),sK1) )).

cnf(u130,negated_conjecture,
    ( k3_tarski(k2_tarski(sK2,k7_subset_1(X0,X0,sK1))) = k7_subset_1(k3_tarski(k2_tarski(sK2,X0)),k3_tarski(k2_tarski(sK2,X0)),sK1) )).

cnf(u96,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) )).

cnf(u95,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK2,sK2,k2_struct_0(sK0)) )).

cnf(u119,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,k4_subset_1(X0,X0,X0)) )).

cnf(u77,axiom,
    ( k1_xboole_0 = k7_subset_1(X3,X3,k3_tarski(k2_tarski(X4,X3))) )).

cnf(u76,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,X1,k3_tarski(k2_tarski(X1,X2))) )).

cnf(u78,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X5) )).

cnf(u75,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u62,axiom,
    ( k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3)) )).

cnf(u107,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u24,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u115,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2) )).

cnf(u114,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1) )).

cnf(u112,negated_conjecture,
    ( k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u111,negated_conjecture,
    ( k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u113,axiom,
    ( k3_tarski(k2_tarski(X0,X0)) = k4_subset_1(X0,X0,X0) )).

cnf(u116,axiom,
    ( k1_xboole_0 = k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) )).

cnf(u110,negated_conjecture,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,sK2)),k3_tarski(k2_tarski(X0,sK2)),sK1) = k3_tarski(k2_tarski(sK2,k7_subset_1(X0,X0,sK1))) )).

cnf(u108,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) )).

cnf(u94,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) )).

cnf(u93,negated_conjecture,
    ( k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)) )).

cnf(u33,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u47,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u98,negated_conjecture,
    ( sK1 = k3_xboole_0(sK1,k2_struct_0(sK0)) )).

cnf(u97,negated_conjecture,
    ( sK2 = k3_xboole_0(sK2,k2_struct_0(sK0)) )).

cnf(u55,axiom,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) )).

cnf(u48,axiom,
    ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 )).

cnf(u40,axiom,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 )).

cnf(u121,axiom,
    ( k3_xboole_0(X2,k4_subset_1(X2,X2,X2)) = X2 )).

cnf(u52,axiom,
    ( k3_xboole_0(X0,k3_tarski(k2_tarski(X1,X0))) = X0 )).

cnf(u42,axiom,
    ( k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = X0 )).

cnf(u31,axiom,
    ( k3_xboole_0(X0,X0) = X0 )).

cnf(u28,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u26,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (15988)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (15980)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.51  % (15980)# SZS output start Saturation.
% 0.20/0.51  cnf(u46,axiom,
% 0.20/0.51      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u27,negated_conjecture,
% 0.20/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u23,negated_conjecture,
% 0.20/0.51      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u87,negated_conjecture,
% 0.20/0.51      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k3_tarski(k2_tarski(X0,sK2))).
% 0.20/0.51  
% 0.20/0.51  cnf(u88,negated_conjecture,
% 0.20/0.51      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k3_tarski(k2_tarski(X1,sK1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u63,axiom,
% 0.20/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u45,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))).
% 0.20/0.51  
% 0.20/0.51  cnf(u89,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k3_tarski(k2_tarski(X2,X3)) = k4_subset_1(X3,X2,X3)).
% 0.20/0.51  
% 0.20/0.51  cnf(u25,negated_conjecture,
% 0.20/0.51      r1_xboole_0(sK1,sK2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u67,axiom,
% 0.20/0.51      ~r1_xboole_0(X0,X1) | k3_tarski(k2_tarski(k7_subset_1(X2,X2,X0),X1)) = k7_subset_1(k3_tarski(k2_tarski(X2,X1)),k3_tarski(k2_tarski(X2,X1)),X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u140,negated_conjecture,
% 0.20/0.51      sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u136,negated_conjecture,
% 0.20/0.51      sK2 = k7_subset_1(sK2,sK2,sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u66,negated_conjecture,
% 0.20/0.51      k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u65,negated_conjecture,
% 0.20/0.51      k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u138,negated_conjecture,
% 0.20/0.51      k4_subset_1(sK2,sK2,sK2) = k7_subset_1(k4_subset_1(sK2,sK2,sK2),k4_subset_1(sK2,sK2,sK2),sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u130,negated_conjecture,
% 0.20/0.51      k3_tarski(k2_tarski(sK2,k7_subset_1(X0,X0,sK1))) = k7_subset_1(k3_tarski(k2_tarski(sK2,X0)),k3_tarski(k2_tarski(sK2,X0)),sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u96,negated_conjecture,
% 0.20/0.51      k1_xboole_0 = k7_subset_1(sK1,sK1,k2_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u95,negated_conjecture,
% 0.20/0.51      k1_xboole_0 = k7_subset_1(sK2,sK2,k2_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u119,axiom,
% 0.20/0.51      k1_xboole_0 = k7_subset_1(X0,X0,k4_subset_1(X0,X0,X0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u77,axiom,
% 0.20/0.51      k1_xboole_0 = k7_subset_1(X3,X3,k3_tarski(k2_tarski(X4,X3)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u76,axiom,
% 0.20/0.51      k1_xboole_0 = k7_subset_1(X1,X1,k3_tarski(k2_tarski(X1,X2)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u78,axiom,
% 0.20/0.51      k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X5)).
% 0.20/0.51  
% 0.20/0.51  cnf(u75,axiom,
% 0.20/0.51      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u62,axiom,
% 0.20/0.51      k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3))).
% 0.20/0.51  
% 0.20/0.51  cnf(u107,negated_conjecture,
% 0.20/0.51      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u24,negated_conjecture,
% 0.20/0.51      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u115,negated_conjecture,
% 0.20/0.51      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u114,negated_conjecture,
% 0.20/0.51      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u112,negated_conjecture,
% 0.20/0.51      k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u111,negated_conjecture,
% 0.20/0.51      k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u113,axiom,
% 0.20/0.51      k3_tarski(k2_tarski(X0,X0)) = k4_subset_1(X0,X0,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u116,axiom,
% 0.20/0.51      k1_xboole_0 = k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u110,negated_conjecture,
% 0.20/0.51      k7_subset_1(k3_tarski(k2_tarski(X0,sK2)),k3_tarski(k2_tarski(X0,sK2)),sK1) = k3_tarski(k2_tarski(sK2,k7_subset_1(X0,X0,sK1)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u108,negated_conjecture,
% 0.20/0.51      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u94,negated_conjecture,
% 0.20/0.51      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u93,negated_conjecture,
% 0.20/0.51      k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2))).
% 0.20/0.51  
% 0.20/0.51  cnf(u33,axiom,
% 0.20/0.51      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u47,axiom,
% 0.20/0.51      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u98,negated_conjecture,
% 0.20/0.51      sK1 = k3_xboole_0(sK1,k2_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u97,negated_conjecture,
% 0.20/0.51      sK2 = k3_xboole_0(sK2,k2_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u55,axiom,
% 0.20/0.51      k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u48,axiom,
% 0.20/0.51      k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0).
% 0.20/0.51  
% 0.20/0.51  cnf(u40,axiom,
% 0.20/0.51      k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0).
% 0.20/0.51  
% 0.20/0.51  cnf(u121,axiom,
% 0.20/0.51      k3_xboole_0(X2,k4_subset_1(X2,X2,X2)) = X2).
% 0.20/0.51  
% 0.20/0.51  cnf(u52,axiom,
% 0.20/0.51      k3_xboole_0(X0,k3_tarski(k2_tarski(X1,X0))) = X0).
% 0.20/0.51  
% 0.20/0.51  cnf(u42,axiom,
% 0.20/0.51      k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = X0).
% 0.20/0.51  
% 0.20/0.51  cnf(u31,axiom,
% 0.20/0.51      k3_xboole_0(X0,X0) = X0).
% 0.20/0.51  
% 0.20/0.51  cnf(u28,axiom,
% 0.20/0.51      k2_subset_1(X0) = X0).
% 0.20/0.51  
% 0.20/0.51  cnf(u26,negated_conjecture,
% 0.20/0.51      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.20/0.51  
% 0.20/0.51  % (15980)# SZS output end Saturation.
% 0.20/0.51  % (15980)------------------------------
% 0.20/0.51  % (15980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (15980)Termination reason: Satisfiable
% 0.20/0.51  
% 0.20/0.51  % (15980)Memory used [KB]: 6268
% 0.20/0.51  % (15980)Time elapsed: 0.034 s
% 0.20/0.51  % (15980)------------------------------
% 0.20/0.51  % (15980)------------------------------
% 0.20/0.52  % (15973)Success in time 0.155 s
%------------------------------------------------------------------------------
