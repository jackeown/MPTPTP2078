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
% DateTime   : Thu Dec  3 13:08:40 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   51 (  51 expanded)
%              Number of leaves         :   51 (  51 expanded)
%              Depth                    :    0
%              Number of atoms          :   93 (  93 expanded)
%              Number of equality atoms :   31 (  31 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u26,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u30,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u41,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) )).

cnf(u25,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u142,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u95,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u27,axiom,
    ( r1_xboole_0(X0,k1_xboole_0) )).

cnf(u34,axiom,
    ( ~ r1_xboole_0(X1,X0)
    | ~ r1_tarski(X1,X0)
    | v1_xboole_0(X1) )).

cnf(u55,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u50,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u76,negated_conjecture,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK1) )).

cnf(u47,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u78,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),X3)
    | ~ r1_tarski(X3,sK1)
    | u1_struct_0(sK0) = X3 )).

cnf(u75,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),X3)
    | ~ r1_tarski(X1,sK1)
    | r2_hidden(sK2(X1,X2),X3)
    | r1_tarski(X1,X2) )).

cnf(u60,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) )).

cnf(u77,negated_conjecture,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(X1,X2)
    | r2_hidden(sK2(X1,X2),u1_struct_0(sK0))
    | ~ r1_tarski(X1,X0) )).

cnf(u97,negated_conjecture,
    ( ~ r1_tarski(X2,sK1)
    | k7_subset_1(u1_struct_0(sK0),X2,X3) = k7_subset_1(X2,X2,X3) )).

cnf(u146,negated_conjecture,
    ( ~ r1_tarski(X0,sK1)
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u144,negated_conjecture,
    ( ~ r1_tarski(X0,u1_struct_0(sK0))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u52,axiom,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) )).

cnf(u61,axiom,
    ( ~ r1_tarski(X1,k1_xboole_0)
    | k1_xboole_0 = X1 )).

cnf(u66,axiom,
    ( ~ r1_tarski(X2,k1_xboole_0)
    | r1_tarski(X2,X3) )).

cnf(u37,axiom,
    ( ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 )).

cnf(u67,axiom,
    ( ~ r1_tarski(X5,X7)
    | r1_tarski(X4,X6)
    | r2_hidden(sK2(X4,X6),X7)
    | ~ r1_tarski(X4,X5) )).

cnf(u94,axiom,
    ( ~ r1_tarski(X2,X1)
    | k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3) )).

cnf(u72,negated_conjecture,
    ( r2_hidden(sK2(X3,X4),u1_struct_0(sK0))
    | r1_tarski(X3,X4)
    | ~ r1_tarski(X3,sK1) )).

cnf(u64,axiom,
    ( r2_hidden(sK2(X0,X1),X2)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,X1) )).

cnf(u39,axiom,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(X0,X1) )).

cnf(u40,axiom,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | r1_tarski(X0,X1) )).

cnf(u38,axiom,
    ( ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1)
    | ~ r1_tarski(X0,X1) )).

cnf(u54,axiom,
    ( ~ r2_hidden(X0,k1_xboole_0) )).

cnf(u53,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u31,axiom,
    ( ~ v1_xboole_0(X0)
    | ~ r2_hidden(X1,X0) )).

cnf(u145,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u143,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u101,negated_conjecture,
    ( sK1 = k7_subset_1(sK1,sK1,k1_xboole_0) )).

cnf(u89,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

cnf(u147,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u93,axiom,
    ( k7_subset_1(X5,k1_xboole_0,X6) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X6))) )).

cnf(u106,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u108,axiom,
    ( k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0) )).

cnf(u104,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,X1) = k7_subset_1(k1_xboole_0,k1_xboole_0,X1) )).

cnf(u96,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u111,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,k1_xboole_0) )).

cnf(u149,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)) )).

cnf(u23,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u45,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

cnf(u90,axiom,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) )).

cnf(u29,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u49,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:07:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (11273)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (11288)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (11270)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (11273)# SZS output start Saturation.
% 0.22/0.51  cnf(u26,negated_conjecture,
% 0.22/0.51      l1_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u30,axiom,
% 0.22/0.51      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.22/0.51  
% 0.22/0.51  cnf(u41,axiom,
% 0.22/0.51      m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u25,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.51  
% 0.22/0.51  cnf(u142,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u42,axiom,
% 0.22/0.51      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u95,axiom,
% 0.22/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u27,axiom,
% 0.22/0.51      r1_xboole_0(X0,k1_xboole_0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u34,axiom,
% 0.22/0.51      ~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u55,axiom,
% 0.22/0.51      r1_tarski(k1_xboole_0,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u50,negated_conjecture,
% 0.22/0.51      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u76,negated_conjecture,
% 0.22/0.51      r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u47,axiom,
% 0.22/0.51      r1_tarski(X1,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u78,negated_conjecture,
% 0.22/0.51      ~r1_tarski(u1_struct_0(sK0),X3) | ~r1_tarski(X3,sK1) | u1_struct_0(sK0) = X3).
% 0.22/0.51  
% 0.22/0.51  cnf(u75,negated_conjecture,
% 0.22/0.51      ~r1_tarski(u1_struct_0(sK0),X3) | ~r1_tarski(X1,sK1) | r2_hidden(sK2(X1,X2),X3) | r1_tarski(X1,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u60,negated_conjecture,
% 0.22/0.51      ~r1_tarski(u1_struct_0(sK0),sK1) | sK1 = u1_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u77,negated_conjecture,
% 0.22/0.51      ~r1_tarski(X0,sK1) | r1_tarski(X1,X2) | r2_hidden(sK2(X1,X2),u1_struct_0(sK0)) | ~r1_tarski(X1,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u97,negated_conjecture,
% 0.22/0.51      ~r1_tarski(X2,sK1) | k7_subset_1(u1_struct_0(sK0),X2,X3) = k7_subset_1(X2,X2,X3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u146,negated_conjecture,
% 0.22/0.51      ~r1_tarski(X0,sK1) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u144,negated_conjecture,
% 0.22/0.51      ~r1_tarski(X0,u1_struct_0(sK0)) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u52,axiom,
% 0.22/0.51      ~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u61,axiom,
% 0.22/0.51      ~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1).
% 0.22/0.51  
% 0.22/0.51  cnf(u66,axiom,
% 0.22/0.51      ~r1_tarski(X2,k1_xboole_0) | r1_tarski(X2,X3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u37,axiom,
% 0.22/0.51      ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1).
% 0.22/0.51  
% 0.22/0.51  cnf(u67,axiom,
% 0.22/0.51      ~r1_tarski(X5,X7) | r1_tarski(X4,X6) | r2_hidden(sK2(X4,X6),X7) | ~r1_tarski(X4,X5)).
% 0.22/0.51  
% 0.22/0.51  cnf(u94,axiom,
% 0.22/0.51      ~r1_tarski(X2,X1) | k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u72,negated_conjecture,
% 0.22/0.51      r2_hidden(sK2(X3,X4),u1_struct_0(sK0)) | r1_tarski(X3,X4) | ~r1_tarski(X3,sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u64,axiom,
% 0.22/0.51      r2_hidden(sK2(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u39,axiom,
% 0.22/0.51      r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u40,axiom,
% 0.22/0.51      ~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u38,axiom,
% 0.22/0.51      ~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u54,axiom,
% 0.22/0.51      ~r2_hidden(X0,k1_xboole_0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u53,axiom,
% 0.22/0.51      v1_xboole_0(k1_xboole_0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u31,axiom,
% 0.22/0.51      ~v1_xboole_0(X0) | ~r2_hidden(X1,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u145,negated_conjecture,
% 0.22/0.51      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u143,negated_conjecture,
% 0.22/0.51      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u101,negated_conjecture,
% 0.22/0.51      sK1 = k7_subset_1(sK1,sK1,k1_xboole_0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u89,negated_conjecture,
% 0.22/0.51      sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u147,negated_conjecture,
% 0.22/0.51      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.22/0.51  
% 0.22/0.51  cnf(u93,axiom,
% 0.22/0.51      k7_subset_1(X5,k1_xboole_0,X6) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X6)))).
% 0.22/0.51  
% 0.22/0.51  cnf(u106,axiom,
% 0.22/0.51      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u108,axiom,
% 0.22/0.51      k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u104,negated_conjecture,
% 0.22/0.51      k7_subset_1(u1_struct_0(sK0),k1_xboole_0,X1) = k7_subset_1(k1_xboole_0,k1_xboole_0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u96,negated_conjecture,
% 0.22/0.51      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u111,axiom,
% 0.22/0.51      k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,k1_xboole_0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u149,negated_conjecture,
% 0.22/0.51      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u23,negated_conjecture,
% 0.22/0.51      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u45,axiom,
% 0.22/0.51      k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u90,axiom,
% 0.22/0.51      k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u29,axiom,
% 0.22/0.51      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u49,negated_conjecture,
% 0.22/0.51      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.22/0.51  
% 0.22/0.51  % (11273)# SZS output end Saturation.
% 0.22/0.51  % (11273)------------------------------
% 0.22/0.51  % (11273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (11273)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (11273)Memory used [KB]: 6268
% 0.22/0.51  % (11273)Time elapsed: 0.090 s
% 0.22/0.51  % (11273)------------------------------
% 0.22/0.51  % (11273)------------------------------
% 0.22/0.52  % (11266)Success in time 0.154 s
%------------------------------------------------------------------------------
