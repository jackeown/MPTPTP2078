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
% DateTime   : Thu Dec  3 13:08:36 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   31 (  31 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    0
%              Number of atoms          :   47 (  47 expanded)
%              Number of equality atoms :   34 (  34 expanded)
%              Maximal clause size      :    2 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u25,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) )).

cnf(u36,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u26,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u59,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u37,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u61,axiom,
    ( r1_tarski(X0,X1)
    | k1_xboole_0 != k7_subset_1(X0,X0,X1) )).

cnf(u38,axiom,
    ( r1_tarski(X0,X0) )).

% (3177)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
cnf(u31,axiom,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 )).

cnf(u60,axiom,
    ( ~ r1_tarski(X0,X1)
    | k1_xboole_0 = k7_subset_1(X0,X0,X1) )).

cnf(u63,axiom,
    ( ~ r1_tarski(X4,X3)
    | k7_subset_1(X3,X4,X5) = k7_subset_1(X4,X4,X5) )).

cnf(u41,negated_conjecture,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) )).

cnf(u40,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u62,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u19,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u21,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u78,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

cnf(u68,axiom,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) )).

cnf(u57,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u46,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u64,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u65,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

cnf(u16,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u67,axiom,
    ( k1_xboole_0 != k7_subset_1(X2,X2,X3)
    | k1_setfam_1(k2_tarski(X2,X3)) = X2 )).

cnf(u81,axiom,
    ( k1_xboole_0 != k7_subset_1(X2,X2,X3)
    | k1_setfam_1(k2_tarski(X3,X2)) = X2 )).

cnf(u84,axiom,
    ( k1_xboole_0 != k7_subset_1(X3,X3,X2)
    | k7_subset_1(X2,X3,X4) = k7_subset_1(X3,X3,X4) )).

cnf(u54,negated_conjecture,
    ( k1_xboole_0 != k5_xboole_0(u1_struct_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) )).

cnf(u103,negated_conjecture,
    ( k1_xboole_0 != k5_xboole_0(u1_struct_0(sK0),sK1)
    | k7_subset_1(sK1,u1_struct_0(sK0),X0) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0) )).

cnf(u48,axiom,
    ( k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))
    | k1_setfam_1(k2_tarski(X1,X0)) = X0 )).

cnf(u42,axiom,
    ( k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 )).

cnf(u35,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (3156)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (3157)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (3157)Refutation not found, incomplete strategy% (3157)------------------------------
% 0.20/0.52  % (3157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3155)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (3164)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (3156)Refutation not found, incomplete strategy% (3156)------------------------------
% 0.20/0.53  % (3156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3149)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (3156)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (3156)Memory used [KB]: 6268
% 0.20/0.53  % (3156)Time elapsed: 0.114 s
% 0.20/0.53  % (3156)------------------------------
% 0.20/0.53  % (3156)------------------------------
% 0.20/0.53  % (3161)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (3149)Refutation not found, incomplete strategy% (3149)------------------------------
% 0.20/0.53  % (3149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3149)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (3149)Memory used [KB]: 1663
% 0.20/0.53  % (3149)Time elapsed: 0.124 s
% 0.20/0.53  % (3149)------------------------------
% 0.20/0.53  % (3149)------------------------------
% 0.20/0.53  % (3164)Refutation not found, incomplete strategy% (3164)------------------------------
% 0.20/0.53  % (3164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3164)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (3164)Memory used [KB]: 6140
% 0.20/0.53  % (3164)Time elapsed: 0.003 s
% 0.20/0.53  % (3164)------------------------------
% 0.20/0.53  % (3164)------------------------------
% 0.20/0.53  % (3171)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (3157)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  % (3161)Refutation not found, incomplete strategy% (3161)------------------------------
% 0.20/0.53  % (3161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3170)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (3150)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  
% 0.20/0.53  % (3157)Memory used [KB]: 10618
% 0.20/0.53  % (3157)Time elapsed: 0.117 s
% 0.20/0.53  % (3157)------------------------------
% 0.20/0.53  % (3157)------------------------------
% 0.20/0.53  % (3151)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (3163)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.54  % (3155)# SZS output start Saturation.
% 0.20/0.54  cnf(u25,axiom,
% 0.20/0.54      m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u36,axiom,
% 0.20/0.54      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.20/0.54  
% 0.20/0.54  cnf(u18,negated_conjecture,
% 0.20/0.54      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.54  
% 0.20/0.54  cnf(u26,axiom,
% 0.20/0.54      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u59,axiom,
% 0.20/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.20/0.54  
% 0.20/0.54  cnf(u37,negated_conjecture,
% 0.20/0.54      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.20/0.54  
% 0.20/0.54  cnf(u61,axiom,
% 0.20/0.54      r1_tarski(X0,X1) | k1_xboole_0 != k7_subset_1(X0,X0,X1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u38,axiom,
% 0.20/0.54      r1_tarski(X0,X0)).
% 0.20/0.54  
% 0.20/0.54  % (3177)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  cnf(u31,axiom,
% 0.20/0.54      ~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0).
% 0.20/0.54  
% 0.20/0.54  cnf(u60,axiom,
% 0.20/0.54      ~r1_tarski(X0,X1) | k1_xboole_0 = k7_subset_1(X0,X0,X1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u63,axiom,
% 0.20/0.54      ~r1_tarski(X4,X3) | k7_subset_1(X3,X4,X5) = k7_subset_1(X4,X4,X5)).
% 0.20/0.54  
% 0.20/0.54  cnf(u41,negated_conjecture,
% 0.20/0.54      sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))).
% 0.20/0.54  
% 0.20/0.54  cnf(u40,axiom,
% 0.20/0.54      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 0.20/0.54  
% 0.20/0.54  cnf(u62,negated_conjecture,
% 0.20/0.54      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u19,axiom,
% 0.20/0.54      k2_subset_1(X0) = X0).
% 0.20/0.54  
% 0.20/0.54  cnf(u21,axiom,
% 0.20/0.54      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u78,negated_conjecture,
% 0.20/0.54      k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u68,axiom,
% 0.20/0.54      k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u57,axiom,
% 0.20/0.54      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 0.20/0.54  
% 0.20/0.54  cnf(u46,axiom,
% 0.20/0.54      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u64,axiom,
% 0.20/0.54      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u65,negated_conjecture,
% 0.20/0.54      k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0))).
% 0.20/0.54  
% 0.20/0.54  cnf(u16,negated_conjecture,
% 0.20/0.54      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u67,axiom,
% 0.20/0.54      k1_xboole_0 != k7_subset_1(X2,X2,X3) | k1_setfam_1(k2_tarski(X2,X3)) = X2).
% 0.20/0.54  
% 0.20/0.54  cnf(u81,axiom,
% 0.20/0.54      k1_xboole_0 != k7_subset_1(X2,X2,X3) | k1_setfam_1(k2_tarski(X3,X2)) = X2).
% 0.20/0.54  
% 0.20/0.54  cnf(u84,axiom,
% 0.20/0.54      k1_xboole_0 != k7_subset_1(X3,X3,X2) | k7_subset_1(X2,X3,X4) = k7_subset_1(X3,X3,X4)).
% 0.20/0.54  
% 0.20/0.54  cnf(u54,negated_conjecture,
% 0.20/0.54      k1_xboole_0 != k5_xboole_0(u1_struct_0(sK0),sK1) | sK1 = u1_struct_0(sK0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u103,negated_conjecture,
% 0.20/0.54      k1_xboole_0 != k5_xboole_0(u1_struct_0(sK0),sK1) | k7_subset_1(sK1,u1_struct_0(sK0),X0) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u48,axiom,
% 0.20/0.54      k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) | k1_setfam_1(k2_tarski(X1,X0)) = X0).
% 0.20/0.54  
% 0.20/0.54  cnf(u42,axiom,
% 0.20/0.54      k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | k1_setfam_1(k2_tarski(X0,X1)) = X0).
% 0.20/0.54  
% 0.20/0.54  cnf(u35,negated_conjecture,
% 0.20/0.54      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.20/0.54  
% 0.20/0.54  % (3155)# SZS output end Saturation.
% 0.20/0.54  % (3155)------------------------------
% 0.20/0.54  % (3155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (3155)Termination reason: Satisfiable
% 0.20/0.54  
% 0.20/0.54  % (3155)Memory used [KB]: 6268
% 0.20/0.54  % (3155)Time elapsed: 0.116 s
% 0.20/0.54  % (3155)------------------------------
% 0.20/0.54  % (3155)------------------------------
% 0.20/0.54  % (3154)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (3165)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (3162)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (3169)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (3170)Refutation not found, incomplete strategy% (3170)------------------------------
% 0.20/0.55  % (3170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (3178)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (3169)Refutation not found, incomplete strategy% (3169)------------------------------
% 0.20/0.55  % (3169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (3169)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (3169)Memory used [KB]: 10746
% 0.20/0.55  % (3169)Time elapsed: 0.127 s
% 0.20/0.55  % (3169)------------------------------
% 0.20/0.55  % (3169)------------------------------
% 0.20/0.55  % (3170)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (3170)Memory used [KB]: 1663
% 0.20/0.55  % (3170)Time elapsed: 0.084 s
% 0.20/0.55  % (3170)------------------------------
% 0.20/0.55  % (3170)------------------------------
% 0.20/0.55  % (3161)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (3161)Memory used [KB]: 6268
% 0.20/0.55  % (3161)Time elapsed: 0.119 s
% 0.20/0.55  % (3161)------------------------------
% 0.20/0.55  % (3161)------------------------------
% 1.46/0.55  % (3148)Success in time 0.188 s
%------------------------------------------------------------------------------
