%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:02 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   62 (  62 expanded)
%              Number of leaves         :   62 (  62 expanded)
%              Depth                    :    0
%              Number of atoms          :   72 (  72 expanded)
%              Number of equality atoms :   52 (  52 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u57,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u36,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u34,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u101,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k3_tarski(k2_tarski(X0,sK2)) )).

cnf(u102,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k3_tarski(k2_tarski(X1,sK1)) )).

cnf(u45,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u74,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u56,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) )).

cnf(u103,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | k4_subset_1(X3,X2,k1_xboole_0) = k3_tarski(k2_tarski(X2,k1_xboole_0)) )).

cnf(u104,axiom,
    ( ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | k4_subset_1(X5,X4,X5) = k3_tarski(k2_tarski(X4,X5)) )).

cnf(u32,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u78,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k3_tarski(k2_tarski(k7_subset_1(X2,X2,X0),X1)) = k7_subset_1(k3_tarski(k2_tarski(X2,X1)),k3_tarski(k2_tarski(X2,X1)),X0) )).

cnf(u60,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u59,negated_conjecture,
    ( r1_tarski(sK2,u1_struct_0(sK0)) )).

cnf(u62,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u61,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u53,axiom,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k2_tarski(X0,X1)) = X1 )).

cnf(u158,negated_conjecture,
    ( sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) )).

cnf(u160,negated_conjecture,
    ( sK2 = k7_subset_1(sK2,sK2,sK1) )).

cnf(u112,negated_conjecture,
    ( sK2 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK2) )).

cnf(u110,negated_conjecture,
    ( sK2 = k4_subset_1(u1_struct_0(sK0),sK2,sK2) )).

cnf(u80,negated_conjecture,
    ( sK2 = k1_setfam_1(k2_tarski(sK2,u1_struct_0(sK0))) )).

cnf(u122,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) )).

cnf(u121,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) )).

cnf(u114,negated_conjecture,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))) )).

cnf(u81,negated_conjecture,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) )).

cnf(u111,negated_conjecture,
    ( k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)) )).

cnf(u31,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u135,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u134,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u66,negated_conjecture,
    ( u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) )).

cnf(u65,negated_conjecture,
    ( u1_struct_0(sK0) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) )).

cnf(u141,axiom,
    ( k1_setfam_1(k2_tarski(X1,k4_subset_1(X1,X1,k1_xboole_0))) = X1 )).

cnf(u51,axiom,
    ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = X0 )).

cnf(u50,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u77,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) )).

cnf(u76,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1) )).

cnf(u137,axiom,
    ( k4_subset_1(X1,X1,X1) = X1 )).

cnf(u136,axiom,
    ( k4_subset_1(X0,k1_xboole_0,X0) = X0 )).

cnf(u129,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,k1_xboole_0) = k4_subset_1(sK2,sK2,k1_xboole_0) )).

cnf(u128,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k4_subset_1(sK1,sK1,k1_xboole_0) )).

cnf(u117,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k3_tarski(k2_tarski(sK2,sK1)) )).

cnf(u120,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK1)) )).

cnf(u109,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK2)) )).

cnf(u35,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u105,negated_conjecture,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,sK1),sK2)) = k7_subset_1(k3_tarski(k2_tarski(X0,sK2)),k3_tarski(k2_tarski(X0,sK2)),sK1) )).

cnf(u126,axiom,
    ( k3_tarski(k2_tarski(X1,k1_xboole_0)) = k4_subset_1(X1,X1,k1_xboole_0) )).

cnf(u64,axiom,
    ( k3_tarski(k2_tarski(X1,X1)) = X1 )).

cnf(u63,axiom,
    ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 )).

cnf(u67,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) )).

% (6228)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
cnf(u91,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK2,sK2,u1_struct_0(sK0)) )).

cnf(u113,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) )).

cnf(u90,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

cnf(u140,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,k4_subset_1(X0,X0,k1_xboole_0)) )).

cnf(u88,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,X1,k3_tarski(k2_tarski(X1,X2))) )).

cnf(u87,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u73,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,k1_xboole_0,X3) )).

cnf(u127,axiom,
    ( k1_xboole_0 = k4_subset_1(X0,k1_xboole_0,k1_xboole_0) )).

cnf(u58,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u71,axiom,
    ( k7_subset_1(X4,X4,X5) = k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X5))) )).

cnf(u33,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:34:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (6229)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (6245)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (6237)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (6229)# SZS output start Saturation.
% 0.21/0.51  cnf(u57,axiom,
% 0.21/0.51      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u36,axiom,
% 0.21/0.51      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u34,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u30,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u101,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k3_tarski(k2_tarski(X0,sK2))).
% 0.21/0.51  
% 0.21/0.51  cnf(u102,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k3_tarski(k2_tarski(X1,sK1))).
% 0.21/0.51  
% 0.21/0.51  cnf(u45,axiom,
% 0.21/0.51      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u74,axiom,
% 0.21/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u56,axiom,
% 0.21/0.51      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))).
% 0.21/0.51  
% 0.21/0.51  cnf(u103,axiom,
% 0.21/0.51      ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k4_subset_1(X3,X2,k1_xboole_0) = k3_tarski(k2_tarski(X2,k1_xboole_0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u104,axiom,
% 0.21/0.51      ~m1_subset_1(X4,k1_zfmisc_1(X5)) | k4_subset_1(X5,X4,X5) = k3_tarski(k2_tarski(X4,X5))).
% 0.21/0.51  
% 0.21/0.51  cnf(u32,negated_conjecture,
% 0.21/0.51      r1_xboole_0(sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u78,axiom,
% 0.21/0.51      ~r1_xboole_0(X0,X1) | k3_tarski(k2_tarski(k7_subset_1(X2,X2,X0),X1)) = k7_subset_1(k3_tarski(k2_tarski(X2,X1)),k3_tarski(k2_tarski(X2,X1)),X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u60,negated_conjecture,
% 0.21/0.51      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u59,negated_conjecture,
% 0.21/0.51      r1_tarski(sK2,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u62,axiom,
% 0.21/0.51      r1_tarski(X1,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u61,axiom,
% 0.21/0.51      r1_tarski(k1_xboole_0,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u53,axiom,
% 0.21/0.51      ~r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1).
% 0.21/0.51  
% 0.21/0.51  cnf(u158,negated_conjecture,
% 0.21/0.51      sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u160,negated_conjecture,
% 0.21/0.51      sK2 = k7_subset_1(sK2,sK2,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u112,negated_conjecture,
% 0.21/0.51      sK2 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u110,negated_conjecture,
% 0.21/0.51      sK2 = k4_subset_1(u1_struct_0(sK0),sK2,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u80,negated_conjecture,
% 0.21/0.51      sK2 = k1_setfam_1(k2_tarski(sK2,u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u122,negated_conjecture,
% 0.21/0.51      sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u121,negated_conjecture,
% 0.21/0.51      sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u114,negated_conjecture,
% 0.21/0.51      sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u81,negated_conjecture,
% 0.21/0.51      sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u111,negated_conjecture,
% 0.21/0.51      k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2))).
% 0.21/0.51  
% 0.21/0.51  cnf(u31,negated_conjecture,
% 0.21/0.51      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u135,negated_conjecture,
% 0.21/0.51      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u134,negated_conjecture,
% 0.21/0.51      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u66,negated_conjecture,
% 0.21/0.51      u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u65,negated_conjecture,
% 0.21/0.51      u1_struct_0(sK0) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u141,axiom,
% 0.21/0.51      k1_setfam_1(k2_tarski(X1,k4_subset_1(X1,X1,k1_xboole_0))) = X1).
% 0.21/0.51  
% 0.21/0.51  cnf(u51,axiom,
% 0.21/0.51      k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = X0).
% 0.21/0.51  
% 0.21/0.51  cnf(u50,axiom,
% 0.21/0.51      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 0.21/0.51  
% 0.21/0.51  cnf(u77,negated_conjecture,
% 0.21/0.51      k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u76,negated_conjecture,
% 0.21/0.51      k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u137,axiom,
% 0.21/0.51      k4_subset_1(X1,X1,X1) = X1).
% 0.21/0.51  
% 0.21/0.51  cnf(u136,axiom,
% 0.21/0.51      k4_subset_1(X0,k1_xboole_0,X0) = X0).
% 0.21/0.51  
% 0.21/0.51  cnf(u129,negated_conjecture,
% 0.21/0.51      k4_subset_1(u1_struct_0(sK0),sK2,k1_xboole_0) = k4_subset_1(sK2,sK2,k1_xboole_0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u128,negated_conjecture,
% 0.21/0.51      k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k4_subset_1(sK1,sK1,k1_xboole_0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u117,negated_conjecture,
% 0.21/0.51      k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k3_tarski(k2_tarski(sK2,sK1))).
% 0.21/0.51  
% 0.21/0.51  cnf(u120,negated_conjecture,
% 0.21/0.51      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK1))).
% 0.21/0.51  
% 0.21/0.51  cnf(u109,negated_conjecture,
% 0.21/0.51      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK2))).
% 0.21/0.51  
% 0.21/0.51  cnf(u35,axiom,
% 0.21/0.51      k2_subset_1(X0) = X0).
% 0.21/0.51  
% 0.21/0.51  cnf(u105,negated_conjecture,
% 0.21/0.51      k3_tarski(k2_tarski(k7_subset_1(X0,X0,sK1),sK2)) = k7_subset_1(k3_tarski(k2_tarski(X0,sK2)),k3_tarski(k2_tarski(X0,sK2)),sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u126,axiom,
% 0.21/0.51      k3_tarski(k2_tarski(X1,k1_xboole_0)) = k4_subset_1(X1,X1,k1_xboole_0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u64,axiom,
% 0.21/0.51      k3_tarski(k2_tarski(X1,X1)) = X1).
% 0.21/0.51  
% 0.21/0.51  cnf(u63,axiom,
% 0.21/0.51      k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0).
% 0.21/0.51  
% 0.21/0.51  cnf(u67,axiom,
% 0.21/0.51      k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))).
% 0.21/0.51  
% 0.21/0.51  % (6228)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  cnf(u91,negated_conjecture,
% 0.21/0.51      k1_xboole_0 = k7_subset_1(sK2,sK2,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u113,negated_conjecture,
% 0.21/0.51      k1_xboole_0 = k7_subset_1(sK1,sK1,k2_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u90,negated_conjecture,
% 0.21/0.51      k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u140,axiom,
% 0.21/0.51      k1_xboole_0 = k7_subset_1(X0,X0,k4_subset_1(X0,X0,k1_xboole_0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u88,axiom,
% 0.21/0.51      k1_xboole_0 = k7_subset_1(X1,X1,k3_tarski(k2_tarski(X1,X2)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u87,axiom,
% 0.21/0.51      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u73,axiom,
% 0.21/0.51      k1_xboole_0 = k7_subset_1(X2,k1_xboole_0,X3)).
% 0.21/0.51  
% 0.21/0.51  cnf(u127,axiom,
% 0.21/0.51      k1_xboole_0 = k4_subset_1(X0,k1_xboole_0,k1_xboole_0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u58,axiom,
% 0.21/0.51      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u71,axiom,
% 0.21/0.51      k7_subset_1(X4,X4,X5) = k5_xboole_0(X4,k1_setfam_1(k2_tarski(X4,X5)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u33,negated_conjecture,
% 0.21/0.51      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.21/0.51  
% 0.21/0.51  % (6229)# SZS output end Saturation.
% 0.21/0.51  % (6229)------------------------------
% 0.21/0.51  % (6229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6229)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (6229)Memory used [KB]: 6268
% 0.21/0.51  % (6229)Time elapsed: 0.099 s
% 0.21/0.51  % (6229)------------------------------
% 0.21/0.51  % (6229)------------------------------
% 0.21/0.52  % (6220)Success in time 0.154 s
%------------------------------------------------------------------------------
