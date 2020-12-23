%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:00 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   44 (  44 expanded)
%              Number of leaves         :   44 (  44 expanded)
%              Depth                    :    0
%              Number of atoms          :   51 (  51 expanded)
%              Number of equality atoms :   40 (  40 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u36,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u80,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2) )).

cnf(u81,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k2_xboole_0(X1,sK1) )).

cnf(u56,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u32,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) )).

cnf(u82,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | k2_xboole_0(X2,X3) = k4_subset_1(X3,X2,X3) )).

cnf(u21,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u60,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k2_xboole_0(k7_subset_1(X2,X2,X0),X1) = k7_subset_1(k2_xboole_0(X2,X1),k2_xboole_0(X2,X1),X0) )).

cnf(u111,negated_conjecture,
    ( sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) )).

cnf(u109,negated_conjecture,
    ( sK2 = k7_subset_1(sK2,sK2,sK1) )).

cnf(u59,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) )).

cnf(u58,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1) )).

cnf(u89,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) )).

cnf(u88,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK2,sK2,k2_struct_0(sK0)) )).

cnf(u62,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,X2,k2_xboole_0(X3,X2)) )).

cnf(u61,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,k2_xboole_0(X0,X1)) )).

cnf(u64,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X7) )).

cnf(u63,axiom,
    ( k1_xboole_0 = k7_subset_1(X4,X4,X4) )).

cnf(u55,axiom,
    ( k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3)) )).

cnf(u104,negated_conjecture,
    ( k2_xboole_0(sK2,k7_subset_1(X0,X0,sK1)) = k7_subset_1(k2_xboole_0(sK2,X0),k2_xboole_0(sK2,X0),sK1) )).

cnf(u118,negated_conjecture,
    ( k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u117,negated_conjecture,
    ( k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u119,axiom,
    ( k2_xboole_0(X0,X0) = k4_subset_1(X0,X0,X0) )).

cnf(u100,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u20,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u90,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK2,k2_struct_0(sK0))) )).

cnf(u91,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_struct_0(sK0))) )).

cnf(u48,axiom,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5)) )).

cnf(u45,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) )).

cnf(u46,axiom,
    ( k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X2,X1))) )).

cnf(u33,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) )).

cnf(u86,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

cnf(u103,negated_conjecture,
    ( k7_subset_1(k2_xboole_0(X0,sK2),k2_xboole_0(X0,sK2),sK1) = k2_xboole_0(sK2,k7_subset_1(X0,X0,sK1)) )).

cnf(u101,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u97,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) )).

cnf(u87,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(sK2,u1_struct_0(sK0)) )).

cnf(u83,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) )).

cnf(u28,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

cnf(u37,axiom,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 )).

cnf(u25,axiom,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u24,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u22,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:15:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (28556)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (28548)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (28542)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (28540)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (28558)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (28538)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (28556)Refutation not found, incomplete strategy% (28556)------------------------------
% 0.21/0.51  % (28556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28556)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (28556)Memory used [KB]: 10746
% 0.21/0.51  % (28556)Time elapsed: 0.062 s
% 0.21/0.51  % (28556)------------------------------
% 0.21/0.51  % (28556)------------------------------
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (28540)# SZS output start Saturation.
% 0.21/0.52  cnf(u36,axiom,
% 0.21/0.52      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u23,negated_conjecture,
% 0.21/0.52      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u19,negated_conjecture,
% 0.21/0.52      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u80,negated_conjecture,
% 0.21/0.52      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u81,negated_conjecture,
% 0.21/0.52      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k2_xboole_0(X1,sK1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u56,axiom,
% 0.21/0.52      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u32,axiom,
% 0.21/0.52      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u82,axiom,
% 0.21/0.52      ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k2_xboole_0(X2,X3) = k4_subset_1(X3,X2,X3)).
% 0.21/0.52  
% 0.21/0.52  cnf(u21,negated_conjecture,
% 0.21/0.52      r1_xboole_0(sK1,sK2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u60,axiom,
% 0.21/0.52      ~r1_xboole_0(X0,X1) | k2_xboole_0(k7_subset_1(X2,X2,X0),X1) = k7_subset_1(k2_xboole_0(X2,X1),k2_xboole_0(X2,X1),X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u111,negated_conjecture,
% 0.21/0.52      sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u109,negated_conjecture,
% 0.21/0.52      sK2 = k7_subset_1(sK2,sK2,sK1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u59,negated_conjecture,
% 0.21/0.52      k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u58,negated_conjecture,
% 0.21/0.52      k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u89,negated_conjecture,
% 0.21/0.52      k1_xboole_0 = k7_subset_1(sK1,sK1,k2_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u88,negated_conjecture,
% 0.21/0.52      k1_xboole_0 = k7_subset_1(sK2,sK2,k2_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u62,axiom,
% 0.21/0.52      k1_xboole_0 = k7_subset_1(X2,X2,k2_xboole_0(X3,X2))).
% 0.21/0.52  
% 0.21/0.52  cnf(u61,axiom,
% 0.21/0.52      k1_xboole_0 = k7_subset_1(X0,X0,k2_xboole_0(X0,X1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u64,axiom,
% 0.21/0.52      k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X7)).
% 0.21/0.52  
% 0.21/0.52  cnf(u63,axiom,
% 0.21/0.52      k1_xboole_0 = k7_subset_1(X4,X4,X4)).
% 0.21/0.52  
% 0.21/0.52  cnf(u55,axiom,
% 0.21/0.52      k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3))).
% 0.21/0.52  
% 0.21/0.52  cnf(u104,negated_conjecture,
% 0.21/0.52      k2_xboole_0(sK2,k7_subset_1(X0,X0,sK1)) = k7_subset_1(k2_xboole_0(sK2,X0),k2_xboole_0(sK2,X0),sK1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u118,negated_conjecture,
% 0.21/0.52      k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u117,negated_conjecture,
% 0.21/0.52      k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u119,axiom,
% 0.21/0.52      k2_xboole_0(X0,X0) = k4_subset_1(X0,X0,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u100,negated_conjecture,
% 0.21/0.52      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u20,negated_conjecture,
% 0.21/0.52      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u90,negated_conjecture,
% 0.21/0.52      k1_xboole_0 = k5_xboole_0(sK2,k3_xboole_0(sK2,k2_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u91,negated_conjecture,
% 0.21/0.52      k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u48,axiom,
% 0.21/0.52      k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X5))).
% 0.21/0.52  
% 0.21/0.52  cnf(u45,axiom,
% 0.21/0.52      k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u46,axiom,
% 0.21/0.52      k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X1,k2_xboole_0(X2,X1)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u33,axiom,
% 0.21/0.52      k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u86,negated_conjecture,
% 0.21/0.52      k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u103,negated_conjecture,
% 0.21/0.52      k7_subset_1(k2_xboole_0(X0,sK2),k2_xboole_0(X0,sK2),sK1) = k2_xboole_0(sK2,k7_subset_1(X0,X0,sK1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u101,negated_conjecture,
% 0.21/0.52      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(sK1,u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u97,negated_conjecture,
% 0.21/0.52      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u87,negated_conjecture,
% 0.21/0.52      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(sK2,u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u83,negated_conjecture,
% 0.21/0.52      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u28,axiom,
% 0.21/0.52      k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u37,axiom,
% 0.21/0.52      k2_xboole_0(k1_xboole_0,X0) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u25,axiom,
% 0.21/0.52      k2_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u24,axiom,
% 0.21/0.52      k2_subset_1(X0) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u22,negated_conjecture,
% 0.21/0.52      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.21/0.52  
% 0.21/0.52  % (28540)# SZS output end Saturation.
% 0.21/0.52  % (28540)------------------------------
% 0.21/0.52  % (28540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28540)Termination reason: Satisfiable
% 0.21/0.52  
% 0.21/0.52  % (28540)Memory used [KB]: 6268
% 0.21/0.52  % (28540)Time elapsed: 0.066 s
% 0.21/0.52  % (28540)------------------------------
% 0.21/0.52  % (28540)------------------------------
% 0.21/0.52  % (28533)Success in time 0.157 s
%------------------------------------------------------------------------------
