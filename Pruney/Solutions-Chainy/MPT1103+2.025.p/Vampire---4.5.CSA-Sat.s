%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:37 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   32 (  32 expanded)
%              Number of leaves         :   32 (  32 expanded)
%              Depth                    :    0
%              Number of atoms          :   40 (  40 expanded)
%              Number of equality atoms :   30 (  30 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u20,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u23,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u36,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u149,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u84,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u85,axiom,
    ( r1_tarski(k7_subset_1(X0,X0,X1),X0) )).

cnf(u40,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u29,axiom,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 )).

cnf(u152,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u150,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u151,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u86,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u21,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u81,axiom,
    ( k1_xboole_0 = k5_xboole_0(k7_subset_1(X0,X0,X1),k1_setfam_1(k2_tarski(k7_subset_1(X0,X0,X1),X0))) )).

cnf(u44,axiom,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) )).

cnf(u49,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) )).

cnf(u38,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k2_xboole_0(X1,X0)))) )).

cnf(u33,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k2_xboole_0(X0,X1)))) )).

cnf(u17,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u119,axiom,
    ( k1_xboole_0 = k7_subset_1(k7_subset_1(X8,X8,X9),k7_subset_1(X8,X8,X9),X8) )).

cnf(u90,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X6) )).

cnf(u104,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,X2,k2_xboole_0(X3,X2)) )).

cnf(u103,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,k2_xboole_0(X0,X1)) )).

cnf(u105,axiom,
    ( k1_xboole_0 = k7_subset_1(X4,X4,X4) )).

cnf(u80,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u83,axiom,
    ( k2_xboole_0(k7_subset_1(X0,X0,X1),X0) = X0 )).

cnf(u82,axiom,
    ( k2_xboole_0(X2,k7_subset_1(X2,X2,X3)) = X2 )).

cnf(u42,axiom,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 )).

cnf(u41,axiom,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 )).

cnf(u25,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

cnf(u35,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:53:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (31084)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (31100)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (31071)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (31075)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (31092)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (31073)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (31092)Refutation not found, incomplete strategy% (31092)------------------------------
% 0.21/0.52  % (31092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31083)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (31093)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (31074)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (31085)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (31093)Refutation not found, incomplete strategy% (31093)------------------------------
% 0.21/0.53  % (31093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31077)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (31093)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31093)Memory used [KB]: 10618
% 0.21/0.53  % (31093)Time elapsed: 0.057 s
% 0.21/0.53  % (31093)------------------------------
% 0.21/0.53  % (31093)------------------------------
% 0.21/0.53  % (31090)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (31076)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.53  % (31072)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (31077)# SZS output start Saturation.
% 0.21/0.54  cnf(u20,negated_conjecture,
% 0.21/0.54      l1_struct_0(sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u23,axiom,
% 0.21/0.54      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.21/0.54  
% 0.21/0.54  cnf(u36,axiom,
% 0.21/0.54      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u19,negated_conjecture,
% 0.21/0.54      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u149,negated_conjecture,
% 0.21/0.54      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u84,axiom,
% 0.21/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u85,axiom,
% 0.21/0.54      r1_tarski(k7_subset_1(X0,X0,X1),X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u40,axiom,
% 0.21/0.54      r1_tarski(k1_xboole_0,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u29,axiom,
% 0.21/0.54      ~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1).
% 0.21/0.54  
% 0.21/0.54  cnf(u152,negated_conjecture,
% 0.21/0.54      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u150,negated_conjecture,
% 0.21/0.54      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.21/0.54  
% 0.21/0.54  cnf(u151,negated_conjecture,
% 0.21/0.54      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u86,negated_conjecture,
% 0.21/0.54      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u21,axiom,
% 0.21/0.54      k2_subset_1(X0) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u81,axiom,
% 0.21/0.54      k1_xboole_0 = k5_xboole_0(k7_subset_1(X0,X0,X1),k1_setfam_1(k2_tarski(k7_subset_1(X0,X0,X1),X0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u44,axiom,
% 0.21/0.54      k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u49,axiom,
% 0.21/0.54      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u38,axiom,
% 0.21/0.54      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k2_xboole_0(X1,X0))))).
% 0.21/0.54  
% 0.21/0.54  cnf(u33,axiom,
% 0.21/0.54      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k2_xboole_0(X0,X1))))).
% 0.21/0.54  
% 0.21/0.54  cnf(u17,negated_conjecture,
% 0.21/0.54      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u119,axiom,
% 0.21/0.54      k1_xboole_0 = k7_subset_1(k7_subset_1(X8,X8,X9),k7_subset_1(X8,X8,X9),X8)).
% 0.21/0.54  
% 0.21/0.54  cnf(u90,axiom,
% 0.21/0.54      k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X6)).
% 0.21/0.54  
% 0.21/0.54  cnf(u104,axiom,
% 0.21/0.54      k1_xboole_0 = k7_subset_1(X2,X2,k2_xboole_0(X3,X2))).
% 0.21/0.54  
% 0.21/0.54  cnf(u103,axiom,
% 0.21/0.54      k1_xboole_0 = k7_subset_1(X0,X0,k2_xboole_0(X0,X1))).
% 0.21/0.54  
% 0.21/0.54  cnf(u105,axiom,
% 0.21/0.54      k1_xboole_0 = k7_subset_1(X4,X4,X4)).
% 0.21/0.54  
% 0.21/0.54  cnf(u80,axiom,
% 0.21/0.54      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u83,axiom,
% 0.21/0.54      k2_xboole_0(k7_subset_1(X0,X0,X1),X0) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u82,axiom,
% 0.21/0.54      k2_xboole_0(X2,k7_subset_1(X2,X2,X3)) = X2).
% 0.21/0.54  
% 0.21/0.54  cnf(u42,axiom,
% 0.21/0.54      k2_xboole_0(X1,k1_xboole_0) = X1).
% 0.21/0.54  
% 0.21/0.54  cnf(u41,axiom,
% 0.21/0.54      k2_xboole_0(k1_xboole_0,X0) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u25,axiom,
% 0.21/0.54      k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u35,negated_conjecture,
% 0.21/0.54      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.54  
% 0.21/0.54  % (31077)# SZS output end Saturation.
% 0.21/0.54  % (31077)------------------------------
% 0.21/0.54  % (31077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31077)Termination reason: Satisfiable
% 0.21/0.54  
% 0.21/0.54  % (31077)Memory used [KB]: 6268
% 0.21/0.54  % (31077)Time elapsed: 0.075 s
% 0.21/0.54  % (31077)------------------------------
% 0.21/0.54  % (31077)------------------------------
% 0.21/0.54  % (31066)Success in time 0.171 s
%------------------------------------------------------------------------------
