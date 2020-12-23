%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:58 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   47 (  47 expanded)
%              Number of leaves         :   47 (  47 expanded)
%              Depth                    :    0
%              Number of atoms          :   55 (  55 expanded)
%              Number of equality atoms :   41 (  41 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u47,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u27,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u80,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k3_tarski(k2_tarski(X0,sK2)) )).

cnf(u81,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k3_tarski(k2_tarski(X1,sK1)) )).

cnf(u62,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u46,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) )).

cnf(u82,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | k3_tarski(k2_tarski(X2,X3)) = k4_subset_1(X3,X2,X3) )).

cnf(u49,negated_conjecture,
    ( r1_xboole_0(sK2,sK1) )).

cnf(u25,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u36,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) )).

cnf(u53,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0 )).

cnf(u99,negated_conjecture,
    ( sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) )).

cnf(u92,negated_conjecture,
    ( sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) )).

cnf(u87,negated_conjecture,
    ( sK2 = k5_xboole_0(k2_struct_0(sK0),sK1) )).

cnf(u96,negated_conjecture,
    ( sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) )).

cnf(u93,negated_conjecture,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))) )).

cnf(u88,negated_conjecture,
    ( sK1 = k5_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u86,negated_conjecture,
    ( k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)) )).

cnf(u104,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u24,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u113,axiom,
    ( k1_setfam_1(k2_tarski(X2,k4_subset_1(X2,X2,X2))) = X2 )).

cnf(u51,axiom,
    ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = X0 )).

cnf(u43,axiom,
    ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = X0 )).

cnf(u41,axiom,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) )).

cnf(u116,axiom,
    ( k7_subset_1(k4_subset_1(X0,X0,X0),k4_subset_1(X0,X0,X0),X0) = k5_xboole_0(k4_subset_1(X0,X0,X0),X0) )).

cnf(u74,axiom,
    ( k7_subset_1(k3_tarski(k2_tarski(X4,X5)),k3_tarski(k2_tarski(X4,X5)),X4) = k5_xboole_0(k3_tarski(k2_tarski(X4,X5)),X4) )).

cnf(u70,axiom,
    ( k7_subset_1(X4,X4,k3_tarski(k2_tarski(X4,X5))) = k5_xboole_0(X4,X4) )).

cnf(u68,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) )).

cnf(u64,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1) )).

cnf(u63,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) )).

cnf(u110,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1) )).

cnf(u109,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2) )).

cnf(u105,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) )).

cnf(u89,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) )).

cnf(u28,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u107,negated_conjecture,
    ( k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u106,negated_conjecture,
    ( k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u108,axiom,
    ( k3_tarski(k2_tarski(X0,X0)) = k4_subset_1(X0,X0,X0) )).

cnf(u42,axiom,
    ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) )).

cnf(u90,negated_conjecture,
    ( k5_xboole_0(sK2,sK2) = k7_subset_1(sK2,sK2,k2_struct_0(sK0)) )).

cnf(u91,negated_conjecture,
    ( k5_xboole_0(sK1,sK1) = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) )).

cnf(u75,axiom,
    ( k7_subset_1(k3_tarski(k2_tarski(X7,X6)),k3_tarski(k2_tarski(X7,X6)),X6) = k5_xboole_0(k3_tarski(k2_tarski(X7,X6)),X6) )).

cnf(u111,axiom,
    ( k5_xboole_0(X0,X0) = k7_subset_1(X0,X0,k4_subset_1(X0,X0,X0)) )).

cnf(u71,axiom,
    ( k7_subset_1(X6,X6,k3_tarski(k2_tarski(X7,X6))) = k5_xboole_0(X6,X6) )).

cnf(u61,axiom,
    ( k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))) )).

cnf(u26,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:26:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (23966)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.50  % (23966)Refutation not found, incomplete strategy% (23966)------------------------------
% 0.21/0.50  % (23966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23966)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  % (23951)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  
% 0.21/0.50  % (23966)Memory used [KB]: 1791
% 0.21/0.50  % (23966)Time elapsed: 0.008 s
% 0.21/0.50  % (23966)------------------------------
% 0.21/0.50  % (23966)------------------------------
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.50  % (23951)# SZS output start Saturation.
% 0.21/0.50  cnf(u47,axiom,
% 0.21/0.50      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u27,negated_conjecture,
% 0.21/0.50      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u23,negated_conjecture,
% 0.21/0.50      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u80,negated_conjecture,
% 0.21/0.50      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k3_tarski(k2_tarski(X0,sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u81,negated_conjecture,
% 0.21/0.50      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k3_tarski(k2_tarski(X1,sK1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u62,axiom,
% 0.21/0.50      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u46,axiom,
% 0.21/0.50      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u82,axiom,
% 0.21/0.50      ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k3_tarski(k2_tarski(X2,X3)) = k4_subset_1(X3,X2,X3)).
% 0.21/0.50  
% 0.21/0.50  cnf(u49,negated_conjecture,
% 0.21/0.50      r1_xboole_0(sK2,sK1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u25,negated_conjecture,
% 0.21/0.50      r1_xboole_0(sK1,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u36,axiom,
% 0.21/0.50      ~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u53,axiom,
% 0.21/0.50      ~r1_xboole_0(X0,X1) | k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0).
% 0.21/0.50  
% 0.21/0.50  cnf(u99,negated_conjecture,
% 0.21/0.50      sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u92,negated_conjecture,
% 0.21/0.50      sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u87,negated_conjecture,
% 0.21/0.50      sK2 = k5_xboole_0(k2_struct_0(sK0),sK1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u96,negated_conjecture,
% 0.21/0.50      sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u93,negated_conjecture,
% 0.21/0.50      sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u88,negated_conjecture,
% 0.21/0.50      sK1 = k5_xboole_0(k2_struct_0(sK0),sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u86,negated_conjecture,
% 0.21/0.50      k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u104,negated_conjecture,
% 0.21/0.50      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u24,negated_conjecture,
% 0.21/0.50      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u113,axiom,
% 0.21/0.50      k1_setfam_1(k2_tarski(X2,k4_subset_1(X2,X2,X2))) = X2).
% 0.21/0.50  
% 0.21/0.50  cnf(u51,axiom,
% 0.21/0.50      k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = X0).
% 0.21/0.50  
% 0.21/0.50  cnf(u43,axiom,
% 0.21/0.50      k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = X0).
% 0.21/0.50  
% 0.21/0.50  cnf(u41,axiom,
% 0.21/0.50      k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u116,axiom,
% 0.21/0.50      k7_subset_1(k4_subset_1(X0,X0,X0),k4_subset_1(X0,X0,X0),X0) = k5_xboole_0(k4_subset_1(X0,X0,X0),X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u74,axiom,
% 0.21/0.50      k7_subset_1(k3_tarski(k2_tarski(X4,X5)),k3_tarski(k2_tarski(X4,X5)),X4) = k5_xboole_0(k3_tarski(k2_tarski(X4,X5)),X4)).
% 0.21/0.50  
% 0.21/0.50  cnf(u70,axiom,
% 0.21/0.50      k7_subset_1(X4,X4,k3_tarski(k2_tarski(X4,X5))) = k5_xboole_0(X4,X4)).
% 0.21/0.50  
% 0.21/0.50  cnf(u68,axiom,
% 0.21/0.50      k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u64,negated_conjecture,
% 0.21/0.50      k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u63,negated_conjecture,
% 0.21/0.50      k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u110,negated_conjecture,
% 0.21/0.50      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u109,negated_conjecture,
% 0.21/0.50      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u105,negated_conjecture,
% 0.21/0.50      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u89,negated_conjecture,
% 0.21/0.50      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u28,axiom,
% 0.21/0.50      k2_subset_1(X0) = X0).
% 0.21/0.50  
% 0.21/0.50  cnf(u107,negated_conjecture,
% 0.21/0.50      k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u106,negated_conjecture,
% 0.21/0.50      k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u108,axiom,
% 0.21/0.50      k3_tarski(k2_tarski(X0,X0)) = k4_subset_1(X0,X0,X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u42,axiom,
% 0.21/0.50      k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u90,negated_conjecture,
% 0.21/0.50      k5_xboole_0(sK2,sK2) = k7_subset_1(sK2,sK2,k2_struct_0(sK0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u91,negated_conjecture,
% 0.21/0.50      k5_xboole_0(sK1,sK1) = k7_subset_1(sK1,sK1,k2_struct_0(sK0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u75,axiom,
% 0.21/0.50      k7_subset_1(k3_tarski(k2_tarski(X7,X6)),k3_tarski(k2_tarski(X7,X6)),X6) = k5_xboole_0(k3_tarski(k2_tarski(X7,X6)),X6)).
% 0.21/0.50  
% 0.21/0.50  cnf(u111,axiom,
% 0.21/0.50      k5_xboole_0(X0,X0) = k7_subset_1(X0,X0,k4_subset_1(X0,X0,X0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u71,axiom,
% 0.21/0.50      k7_subset_1(X6,X6,k3_tarski(k2_tarski(X7,X6))) = k5_xboole_0(X6,X6)).
% 0.21/0.50  
% 0.21/0.50  cnf(u61,axiom,
% 0.21/0.50      k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u26,negated_conjecture,
% 0.21/0.50      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.21/0.50  
% 0.21/0.50  % (23951)# SZS output end Saturation.
% 0.21/0.50  % (23951)------------------------------
% 0.21/0.50  % (23951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23951)Termination reason: Satisfiable
% 0.21/0.50  
% 0.21/0.50  % (23951)Memory used [KB]: 6268
% 0.21/0.50  % (23951)Time elapsed: 0.030 s
% 0.21/0.50  % (23951)------------------------------
% 0.21/0.50  % (23951)------------------------------
% 0.21/0.51  % (23944)Success in time 0.149 s
%------------------------------------------------------------------------------
