%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:01 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   47 (  47 expanded)
%              Number of leaves         :   47 (  47 expanded)
%              Depth                    :    0
%              Number of atoms          :   56 (  56 expanded)
%              Number of equality atoms :   43 (  43 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u45,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u28,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u92,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2) )).

cnf(u93,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k2_xboole_0(X1,sK1) )).

cnf(u36,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u60,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u59,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u39,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) )).

cnf(u94,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | k2_xboole_0(X2,X3) = k4_subset_1(X3,X2,X3) )).

cnf(u26,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u37,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u47,negated_conjecture,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) )).

cnf(u102,negated_conjecture,
    ( sK1 = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(k2_struct_0(sK0),sK2)) )).

cnf(u101,negated_conjecture,
    ( sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) )).

cnf(u73,negated_conjecture,
    ( sK1 = k7_subset_1(sK1,sK1,sK2) )).

cnf(u48,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u98,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

cnf(u25,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u72,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u83,axiom,
    ( k7_subset_1(X2,X2,X3) = k7_subset_1(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3),X3) )).

cnf(u63,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) )).

cnf(u62,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1) )).

cnf(u107,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u106,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) )).

cnf(u105,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1) )).

cnf(u97,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(u1_struct_0(sK0),sK2) )).

cnf(u95,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) )).

cnf(u68,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

cnf(u67,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK2) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) )).

cnf(u51,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u50,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK2) = k5_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u66,axiom,
    ( k3_subset_1(X0,X0) = k7_subset_1(X0,X0,X0) )).

cnf(u52,axiom,
    ( k3_subset_1(X0,X0) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) )).

cnf(u49,axiom,
    ( k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 )).

cnf(u29,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u109,negated_conjecture,
    ( k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u108,negated_conjecture,
    ( k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u110,axiom,
    ( k2_xboole_0(X0,X0) = k4_subset_1(X0,X0,X0) )).

cnf(u86,axiom,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u61,axiom,
    ( k5_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X1),X1)) = k7_subset_1(X0,X0,X1) )).

cnf(u58,axiom,
    ( k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3)) )).

cnf(u44,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u54,axiom,
    ( k1_xboole_0 = k3_subset_1(k1_xboole_0,k1_xboole_0) )).

cnf(u46,negated_conjecture,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2) )).

cnf(u30,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u27,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:20:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (11084)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (11084)Refutation not found, incomplete strategy% (11084)------------------------------
% 0.21/0.51  % (11084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11094)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (11084)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11084)Memory used [KB]: 1791
% 0.21/0.51  % (11084)Time elapsed: 0.094 s
% 0.21/0.51  % (11084)------------------------------
% 0.21/0.51  % (11084)------------------------------
% 0.21/0.51  % (11094)Refutation not found, incomplete strategy% (11094)------------------------------
% 0.21/0.51  % (11094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11094)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11094)Memory used [KB]: 10618
% 0.21/0.51  % (11094)Time elapsed: 0.106 s
% 0.21/0.51  % (11094)------------------------------
% 0.21/0.51  % (11094)------------------------------
% 0.21/0.51  % (11109)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (11092)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (11088)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (11108)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (11092)Refutation not found, incomplete strategy% (11092)------------------------------
% 0.21/0.52  % (11092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11092)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11092)Memory used [KB]: 10746
% 0.21/0.52  % (11092)Time elapsed: 0.116 s
% 0.21/0.52  % (11092)------------------------------
% 0.21/0.52  % (11092)------------------------------
% 0.21/0.52  % (11091)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (11099)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (11105)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (11086)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (11090)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (11086)Refutation not found, incomplete strategy% (11086)------------------------------
% 0.21/0.53  % (11086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11086)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11086)Memory used [KB]: 10746
% 0.21/0.53  % (11086)Time elapsed: 0.126 s
% 0.21/0.53  % (11086)------------------------------
% 0.21/0.53  % (11086)------------------------------
% 0.21/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.53  % (11090)# SZS output start Saturation.
% 0.21/0.53  cnf(u45,axiom,
% 0.21/0.53      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u28,negated_conjecture,
% 0.21/0.53      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.53  
% 0.21/0.53  cnf(u24,negated_conjecture,
% 0.21/0.53      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.53  
% 0.21/0.53  cnf(u92,negated_conjecture,
% 0.21/0.53      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u93,negated_conjecture,
% 0.21/0.53      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k2_xboole_0(X1,sK1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u36,axiom,
% 0.21/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.21/0.53  
% 0.21/0.53  cnf(u60,axiom,
% 0.21/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u59,axiom,
% 0.21/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u39,axiom,
% 0.21/0.53      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u94,axiom,
% 0.21/0.53      ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k2_xboole_0(X2,X3) = k4_subset_1(X3,X2,X3)).
% 0.21/0.53  
% 0.21/0.53  cnf(u26,negated_conjecture,
% 0.21/0.53      r1_xboole_0(sK1,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u37,axiom,
% 0.21/0.53      ~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0).
% 0.21/0.53  
% 0.21/0.53  cnf(u47,negated_conjecture,
% 0.21/0.53      sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))).
% 0.21/0.53  
% 0.21/0.53  cnf(u102,negated_conjecture,
% 0.21/0.53      sK1 = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(k2_struct_0(sK0),sK2))).
% 0.21/0.53  
% 0.21/0.53  cnf(u101,negated_conjecture,
% 0.21/0.53      sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u73,negated_conjecture,
% 0.21/0.53      sK1 = k7_subset_1(sK1,sK1,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u48,negated_conjecture,
% 0.21/0.53      sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.21/0.53  
% 0.21/0.53  cnf(u98,negated_conjecture,
% 0.21/0.53      k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u25,negated_conjecture,
% 0.21/0.53      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u72,axiom,
% 0.21/0.53      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u83,axiom,
% 0.21/0.53      k7_subset_1(X2,X2,X3) = k7_subset_1(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3),X3)).
% 0.21/0.53  
% 0.21/0.53  cnf(u63,negated_conjecture,
% 0.21/0.53      k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u62,negated_conjecture,
% 0.21/0.53      k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u107,negated_conjecture,
% 0.21/0.53      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),sK1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u106,negated_conjecture,
% 0.21/0.53      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u105,negated_conjecture,
% 0.21/0.53      k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u97,negated_conjecture,
% 0.21/0.53      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(u1_struct_0(sK0),sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u95,negated_conjecture,
% 0.21/0.53      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u68,negated_conjecture,
% 0.21/0.53      k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u67,negated_conjecture,
% 0.21/0.53      k3_subset_1(u1_struct_0(sK0),sK2) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u51,negated_conjecture,
% 0.21/0.53      k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),sK1))).
% 0.21/0.53  
% 0.21/0.53  cnf(u50,negated_conjecture,
% 0.21/0.53      k3_subset_1(u1_struct_0(sK0),sK2) = k5_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),sK2))).
% 0.21/0.53  
% 0.21/0.53  cnf(u66,axiom,
% 0.21/0.53      k3_subset_1(X0,X0) = k7_subset_1(X0,X0,X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u52,axiom,
% 0.21/0.53      k3_subset_1(X0,X0) = k5_xboole_0(X0,k3_xboole_0(X0,X0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u49,axiom,
% 0.21/0.53      k3_subset_1(X0,k3_subset_1(X0,X0)) = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u29,axiom,
% 0.21/0.53      k2_subset_1(X0) = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u109,negated_conjecture,
% 0.21/0.53      k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u108,negated_conjecture,
% 0.21/0.53      k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u110,axiom,
% 0.21/0.53      k2_xboole_0(X0,X0) = k4_subset_1(X0,X0,X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u86,axiom,
% 0.21/0.53      k2_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u61,axiom,
% 0.21/0.53      k5_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X1),X1)) = k7_subset_1(X0,X0,X1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u58,axiom,
% 0.21/0.53      k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3))).
% 0.21/0.53  
% 0.21/0.53  cnf(u44,axiom,
% 0.21/0.53      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u54,axiom,
% 0.21/0.53      k1_xboole_0 = k3_subset_1(k1_xboole_0,k1_xboole_0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u46,negated_conjecture,
% 0.21/0.53      k1_xboole_0 = k3_xboole_0(sK1,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u30,axiom,
% 0.21/0.53      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u27,negated_conjecture,
% 0.21/0.53      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.21/0.53  
% 0.21/0.53  % (11090)# SZS output end Saturation.
% 0.21/0.53  % (11090)------------------------------
% 0.21/0.53  % (11090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11090)Termination reason: Satisfiable
% 0.21/0.53  
% 0.21/0.53  % (11090)Memory used [KB]: 6268
% 0.21/0.53  % (11090)Time elapsed: 0.126 s
% 0.21/0.53  % (11090)------------------------------
% 0.21/0.53  % (11090)------------------------------
% 0.21/0.53  % (11081)Success in time 0.17 s
%------------------------------------------------------------------------------
