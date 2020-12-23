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
% DateTime   : Thu Dec  3 13:08:58 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   48 (  48 expanded)
%              Number of leaves         :   48 (  48 expanded)
%              Depth                    :    0
%              Number of atoms          :   55 (  55 expanded)
%              Number of equality atoms :   44 (  44 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u42,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u26,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u129,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2) )).

cnf(u130,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k2_xboole_0(X1,sK1) )).

cnf(u56,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u37,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) )).

cnf(u131,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | k2_xboole_0(X2,X3) = k4_subset_1(X3,X2,X3) )).

% (28716)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
cnf(u24,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u35,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u141,negated_conjecture,
    ( sK2 = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(sK1,k2_struct_0(sK0))) )).

cnf(u142,negated_conjecture,
    ( sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) )).

cnf(u78,negated_conjecture,
    ( sK2 = k7_subset_1(sK2,sK2,sK1) )).

cnf(u144,negated_conjecture,
    ( sK1 = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(sK2,k2_struct_0(sK0))) )).

cnf(u143,negated_conjecture,
    ( sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) )).

cnf(u67,negated_conjecture,
    ( sK1 = k7_subset_1(sK1,sK1,sK2) )).

cnf(u135,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

cnf(u149,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u23,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u79,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(k2_xboole_0(X1,X0),k3_xboole_0(X1,k2_xboole_0(X1,X0))) )).

cnf(u61,axiom,
    ( k7_subset_1(X1,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) )).

cnf(u65,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u103,axiom,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(k2_xboole_0(X1,X0),k2_xboole_0(X1,X0),X1) )).

cnf(u82,axiom,
    ( k7_subset_1(X2,X2,X3) = k7_subset_1(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3),X3) )).

cnf(u59,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) )).

cnf(u58,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1) )).

cnf(u150,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u136,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(sK2,u1_struct_0(sK0)) )).

cnf(u146,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) )).

cnf(u132,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) )).

cnf(u27,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u57,axiom,
    ( k5_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X1,k2_xboole_0(X0,X1))) = k7_subset_1(X0,X0,X1) )).

cnf(u55,axiom,
    ( k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3)) )).

cnf(u41,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u96,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) )).

cnf(u99,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u66,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X5) )).

cnf(u52,negated_conjecture,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2) )).

cnf(u44,axiom,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

cnf(u28,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u32,axiom,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

cnf(u155,negated_conjecture,
    ( k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u156,negated_conjecture,
    ( k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u86,axiom,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 )).

cnf(u157,axiom,
    ( k2_xboole_0(X0,X0) = k4_subset_1(X0,X0,X0) )).

cnf(u85,axiom,
    ( k2_xboole_0(X4,k1_xboole_0) = X4 )).

cnf(u31,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

cnf(u25,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:40:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (28702)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (28702)Refutation not found, incomplete strategy% (28702)------------------------------
% 0.21/0.52  % (28702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28707)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (28702)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28702)Memory used [KB]: 1791
% 0.21/0.52  % (28702)Time elapsed: 0.104 s
% 0.21/0.52  % (28702)------------------------------
% 0.21/0.52  % (28702)------------------------------
% 0.21/0.52  % (28709)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (28724)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (28724)Refutation not found, incomplete strategy% (28724)------------------------------
% 0.21/0.52  % (28724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28707)Refutation not found, incomplete strategy% (28707)------------------------------
% 0.21/0.52  % (28707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28707)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28707)Memory used [KB]: 6268
% 0.21/0.52  % (28707)Time elapsed: 0.121 s
% 0.21/0.52  % (28707)------------------------------
% 0.21/0.52  % (28707)------------------------------
% 0.21/0.53  % (28708)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (28724)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (28724)Memory used [KB]: 10746
% 0.21/0.53  % (28724)Time elapsed: 0.116 s
% 0.21/0.53  % (28724)------------------------------
% 0.21/0.53  % (28724)------------------------------
% 0.21/0.53  % (28710)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.53  % (28714)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (28720)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (28704)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (28708)# SZS output start Saturation.
% 0.21/0.53  cnf(u42,axiom,
% 0.21/0.53      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u26,negated_conjecture,
% 0.21/0.53      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.53  
% 0.21/0.53  cnf(u22,negated_conjecture,
% 0.21/0.53      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.53  
% 0.21/0.53  cnf(u129,negated_conjecture,
% 0.21/0.53      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u130,negated_conjecture,
% 0.21/0.53      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k2_xboole_0(X1,sK1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u56,axiom,
% 0.21/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u37,axiom,
% 0.21/0.53      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u131,axiom,
% 0.21/0.53      ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k2_xboole_0(X2,X3) = k4_subset_1(X3,X2,X3)).
% 0.21/0.53  
% 0.21/0.54  % (28716)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  cnf(u24,negated_conjecture,
% 0.21/0.54      r1_xboole_0(sK1,sK2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u35,axiom,
% 0.21/0.54      ~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0).
% 0.21/0.54  
% 0.21/0.54  cnf(u141,negated_conjecture,
% 0.21/0.54      sK2 = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(sK1,k2_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u142,negated_conjecture,
% 0.21/0.54      sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u78,negated_conjecture,
% 0.21/0.54      sK2 = k7_subset_1(sK2,sK2,sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u144,negated_conjecture,
% 0.21/0.54      sK1 = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(sK2,k2_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u143,negated_conjecture,
% 0.21/0.54      sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u67,negated_conjecture,
% 0.21/0.54      sK1 = k7_subset_1(sK1,sK1,sK2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u135,negated_conjecture,
% 0.21/0.54      k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u149,negated_conjecture,
% 0.21/0.54      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u23,negated_conjecture,
% 0.21/0.54      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u79,axiom,
% 0.21/0.54      k7_subset_1(X0,X0,X1) = k5_xboole_0(k2_xboole_0(X1,X0),k3_xboole_0(X1,k2_xboole_0(X1,X0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u61,axiom,
% 0.21/0.54      k7_subset_1(X1,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))).
% 0.21/0.54  
% 0.21/0.54  cnf(u65,axiom,
% 0.21/0.54      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u103,axiom,
% 0.21/0.54      k7_subset_1(X0,X0,X1) = k7_subset_1(k2_xboole_0(X1,X0),k2_xboole_0(X1,X0),X1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u82,axiom,
% 0.21/0.54      k7_subset_1(X2,X2,X3) = k7_subset_1(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3),X3)).
% 0.21/0.54  
% 0.21/0.54  cnf(u59,negated_conjecture,
% 0.21/0.54      k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u58,negated_conjecture,
% 0.21/0.54      k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u150,negated_conjecture,
% 0.21/0.54      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(sK1,u1_struct_0(sK0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u136,negated_conjecture,
% 0.21/0.54      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(sK2,u1_struct_0(sK0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u146,negated_conjecture,
% 0.21/0.54      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u132,negated_conjecture,
% 0.21/0.54      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u27,axiom,
% 0.21/0.54      k2_subset_1(X0) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u57,axiom,
% 0.21/0.54      k5_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X1,k2_xboole_0(X0,X1))) = k7_subset_1(X0,X0,X1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u55,axiom,
% 0.21/0.54      k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3))).
% 0.21/0.54  
% 0.21/0.54  cnf(u41,axiom,
% 0.21/0.54      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u96,axiom,
% 0.21/0.54      k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u99,axiom,
% 0.21/0.54      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u66,axiom,
% 0.21/0.54      k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X5)).
% 0.21/0.54  
% 0.21/0.54  cnf(u52,negated_conjecture,
% 0.21/0.54      k1_xboole_0 = k3_xboole_0(sK1,sK2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u44,axiom,
% 0.21/0.54      k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u28,axiom,
% 0.21/0.54      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u32,axiom,
% 0.21/0.54      k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u155,negated_conjecture,
% 0.21/0.54      k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u156,negated_conjecture,
% 0.21/0.54      k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u86,axiom,
% 0.21/0.54      k2_xboole_0(k1_xboole_0,X1) = X1).
% 0.21/0.54  
% 0.21/0.54  cnf(u157,axiom,
% 0.21/0.54      k2_xboole_0(X0,X0) = k4_subset_1(X0,X0,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u85,axiom,
% 0.21/0.54      k2_xboole_0(X4,k1_xboole_0) = X4).
% 0.21/0.54  
% 0.21/0.54  cnf(u31,axiom,
% 0.21/0.54      k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u25,negated_conjecture,
% 0.21/0.54      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.21/0.54  
% 0.21/0.54  % (28708)# SZS output end Saturation.
% 0.21/0.54  % (28708)------------------------------
% 0.21/0.54  % (28708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28708)Termination reason: Satisfiable
% 0.21/0.54  
% 0.21/0.54  % (28708)Memory used [KB]: 6268
% 0.21/0.54  % (28708)Time elapsed: 0.114 s
% 0.21/0.54  % (28708)------------------------------
% 0.21/0.54  % (28708)------------------------------
% 0.21/0.54  % (28704)Refutation not found, incomplete strategy% (28704)------------------------------
% 0.21/0.54  % (28704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28704)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28704)Memory used [KB]: 10746
% 0.21/0.54  % (28704)Time elapsed: 0.129 s
% 0.21/0.54  % (28704)------------------------------
% 0.21/0.54  % (28704)------------------------------
% 0.21/0.54  % (28718)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (28725)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (28712)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (28728)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (28710)Refutation not found, incomplete strategy% (28710)------------------------------
% 0.21/0.54  % (28710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28710)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28710)Memory used [KB]: 10746
% 0.21/0.54  % (28710)Time elapsed: 0.117 s
% 0.21/0.54  % (28710)------------------------------
% 0.21/0.54  % (28710)------------------------------
% 0.21/0.54  % (28703)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (28712)Refutation not found, incomplete strategy% (28712)------------------------------
% 0.21/0.54  % (28712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28728)Refutation not found, incomplete strategy% (28728)------------------------------
% 0.21/0.54  % (28728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28728)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28728)Memory used [KB]: 10746
% 0.21/0.54  % (28728)Time elapsed: 0.131 s
% 0.21/0.54  % (28728)------------------------------
% 0.21/0.54  % (28728)------------------------------
% 0.21/0.54  % (28712)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28712)Memory used [KB]: 10618
% 0.21/0.54  % (28712)Time elapsed: 0.127 s
% 0.21/0.54  % (28712)------------------------------
% 0.21/0.54  % (28712)------------------------------
% 0.21/0.54  % (28730)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (28709)Refutation not found, incomplete strategy% (28709)------------------------------
% 0.21/0.54  % (28709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28709)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28709)Memory used [KB]: 6268
% 0.21/0.54  % (28709)Time elapsed: 0.139 s
% 0.21/0.54  % (28709)------------------------------
% 0.21/0.54  % (28709)------------------------------
% 0.21/0.54  % (28711)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (28715)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (28731)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (28701)Success in time 0.18 s
%------------------------------------------------------------------------------
