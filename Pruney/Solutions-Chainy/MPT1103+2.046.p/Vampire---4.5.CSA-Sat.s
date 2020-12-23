%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:40 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   39 (  39 expanded)
%              Number of leaves         :   39 (  39 expanded)
%              Depth                    :    0
%              Number of atoms          :   85 (  85 expanded)
%              Number of equality atoms :   45 (  45 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u32,axiom,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) )).

cnf(u52,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u27,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u47,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u37,axiom,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | r2_hidden(X0,X1) )).

cnf(u58,negated_conjecture,
    ( r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u84,axiom,
    ( r2_hidden(sK2(X5,k1_zfmisc_1(X4)),k1_zfmisc_1(X4))
    | k1_xboole_0 = k4_xboole_0(sK2(X5,k1_zfmisc_1(X4)),X5)
    | k1_zfmisc_1(X5) = k1_zfmisc_1(X4) )).

cnf(u71,axiom,
    ( r2_hidden(sK2(X4,k1_zfmisc_1(X5)),k1_zfmisc_1(X4))
    | k1_zfmisc_1(X5) = k1_zfmisc_1(X4)
    | r1_tarski(sK2(X4,k1_zfmisc_1(X5)),X5) )).

cnf(u87,axiom,
    ( r2_hidden(sK2(X5,k1_zfmisc_1(X4)),k1_zfmisc_1(X5))
    | k1_xboole_0 = k4_xboole_0(sK2(X5,k1_zfmisc_1(X4)),X4)
    | k1_zfmisc_1(X5) = k1_zfmisc_1(X4) )).

cnf(u43,axiom,
    ( r2_hidden(sK2(X0,X1),X1)
    | r1_tarski(sK2(X0,X1),X0)
    | k1_zfmisc_1(X0) = X1 )).

cnf(u54,axiom,
    ( r2_hidden(X0,k1_zfmisc_1(X0)) )).

cnf(u44,axiom,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | ~ r1_tarski(sK2(X0,X1),X0)
    | k1_zfmisc_1(X0) = X1 )).

cnf(u51,axiom,
    ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
    | r1_tarski(X3,X0) )).

cnf(u66,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u63,axiom,
    ( r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X0)
    | r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) )).

cnf(u70,axiom,
    ( r1_tarski(sK2(X2,k1_zfmisc_1(X3)),X3)
    | k1_zfmisc_1(X3) = k1_zfmisc_1(X2)
    | k1_xboole_0 = k4_xboole_0(sK2(X2,k1_zfmisc_1(X3)),X2) )).

cnf(u63_001,axiom,
    ( r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X0)
    | r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) )).

cnf(u73,axiom,
    ( r1_tarski(sK2(X2,k1_zfmisc_1(X3)),X2)
    | k1_zfmisc_1(X3) = k1_zfmisc_1(X2)
    | k1_xboole_0 = k4_xboole_0(sK2(X2,k1_zfmisc_1(X3)),X3) )).

cnf(u48,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u76,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) )).

cnf(u72,axiom,
    ( ~ r1_tarski(X1,sK2(X0,k1_zfmisc_1(X1)))
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | sK2(X0,k1_zfmisc_1(X1)) = X1
    | r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X0) )).

cnf(u82,axiom,
    ( ~ r1_tarski(X0,sK2(X1,k1_zfmisc_1(X0)))
    | k1_xboole_0 = k4_xboole_0(sK2(X1,k1_zfmisc_1(X0)),X1)
    | sK2(X1,k1_zfmisc_1(X0)) = X0
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) )).

cnf(u69,axiom,
    ( ~ r1_tarski(X0,sK2(X0,k1_zfmisc_1(X1)))
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | sK2(X0,k1_zfmisc_1(X1)) = X0
    | r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1) )).

cnf(u85,axiom,
    ( ~ r1_tarski(X1,sK2(X1,k1_zfmisc_1(X0)))
    | k1_xboole_0 = k4_xboole_0(sK2(X1,k1_zfmisc_1(X0)),X0)
    | sK2(X1,k1_zfmisc_1(X0)) = X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) )).

cnf(u50,axiom,
    ( ~ r1_tarski(X3,X0)
    | r2_hidden(X3,k1_zfmisc_1(X0)) )).

cnf(u46,axiom,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u40,axiom,
    ( ~ r1_tarski(X1,X0)
    | X0 = X1
    | ~ r1_tarski(X0,X1) )).

cnf(u61,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u33,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u35,axiom,
    ( k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) )).

cnf(u83,axiom,
    ( k1_xboole_0 = k4_xboole_0(sK2(X3,k1_zfmisc_1(X2)),X3)
    | k1_xboole_0 = k4_xboole_0(sK2(X3,k1_zfmisc_1(X2)),X2)
    | k1_zfmisc_1(X3) = k1_zfmisc_1(X2) )).

% (12935)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
cnf(u83_002,axiom,
    ( k1_xboole_0 = k4_xboole_0(sK2(X3,k1_zfmisc_1(X2)),X3)
    | k1_xboole_0 = k4_xboole_0(sK2(X3,k1_zfmisc_1(X2)),X2)
    | k1_zfmisc_1(X3) = k1_zfmisc_1(X2) )).

cnf(u77,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u59,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u31,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u62,axiom,
    ( k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u36,axiom,
    ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

cnf(u45,axiom,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) )).

cnf(u28,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 != k2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (12938)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.50  % (12954)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.50  % (12957)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (12932)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (12932)Refutation not found, incomplete strategy% (12932)------------------------------
% 0.20/0.51  % (12932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12946)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (12941)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.51  % (12932)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (12932)Memory used [KB]: 1663
% 0.20/0.51  % (12932)Time elapsed: 0.106 s
% 0.20/0.51  % (12932)------------------------------
% 0.20/0.51  % (12932)------------------------------
% 0.20/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.51  % (12938)# SZS output start Saturation.
% 0.20/0.51  cnf(u32,axiom,
% 0.20/0.51      ~v1_xboole_0(k1_zfmisc_1(X0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u52,axiom,
% 0.20/0.51      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u27,negated_conjecture,
% 0.20/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u47,axiom,
% 0.20/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u37,axiom,
% 0.20/0.51      ~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u58,negated_conjecture,
% 0.20/0.51      r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u84,axiom,
% 0.20/0.51      r2_hidden(sK2(X5,k1_zfmisc_1(X4)),k1_zfmisc_1(X4)) | k1_xboole_0 = k4_xboole_0(sK2(X5,k1_zfmisc_1(X4)),X5) | k1_zfmisc_1(X5) = k1_zfmisc_1(X4)).
% 0.20/0.51  
% 0.20/0.51  cnf(u71,axiom,
% 0.20/0.51      r2_hidden(sK2(X4,k1_zfmisc_1(X5)),k1_zfmisc_1(X4)) | k1_zfmisc_1(X5) = k1_zfmisc_1(X4) | r1_tarski(sK2(X4,k1_zfmisc_1(X5)),X5)).
% 0.20/0.51  
% 0.20/0.51  cnf(u87,axiom,
% 0.20/0.51      r2_hidden(sK2(X5,k1_zfmisc_1(X4)),k1_zfmisc_1(X5)) | k1_xboole_0 = k4_xboole_0(sK2(X5,k1_zfmisc_1(X4)),X4) | k1_zfmisc_1(X5) = k1_zfmisc_1(X4)).
% 0.20/0.51  
% 0.20/0.51  cnf(u43,axiom,
% 0.20/0.51      r2_hidden(sK2(X0,X1),X1) | r1_tarski(sK2(X0,X1),X0) | k1_zfmisc_1(X0) = X1).
% 0.20/0.51  
% 0.20/0.51  cnf(u54,axiom,
% 0.20/0.51      r2_hidden(X0,k1_zfmisc_1(X0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u44,axiom,
% 0.20/0.51      ~r2_hidden(sK2(X0,X1),X1) | ~r1_tarski(sK2(X0,X1),X0) | k1_zfmisc_1(X0) = X1).
% 0.20/0.51  
% 0.20/0.51  cnf(u51,axiom,
% 0.20/0.51      ~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u66,negated_conjecture,
% 0.20/0.51      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u63,axiom,
% 0.20/0.51      r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X0) | r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1) | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u70,axiom,
% 0.20/0.51      r1_tarski(sK2(X2,k1_zfmisc_1(X3)),X3) | k1_zfmisc_1(X3) = k1_zfmisc_1(X2) | k1_xboole_0 = k4_xboole_0(sK2(X2,k1_zfmisc_1(X3)),X2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u63,axiom,
% 0.20/0.51      r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X0) | r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1) | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u73,axiom,
% 0.20/0.51      r1_tarski(sK2(X2,k1_zfmisc_1(X3)),X2) | k1_zfmisc_1(X3) = k1_zfmisc_1(X2) | k1_xboole_0 = k4_xboole_0(sK2(X2,k1_zfmisc_1(X3)),X3)).
% 0.20/0.51  
% 0.20/0.51  cnf(u48,axiom,
% 0.20/0.51      r1_tarski(X1,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u76,negated_conjecture,
% 0.20/0.51      ~r1_tarski(u1_struct_0(sK0),sK1) | sK1 = u1_struct_0(sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u72,axiom,
% 0.20/0.51      ~r1_tarski(X1,sK2(X0,k1_zfmisc_1(X1))) | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) | sK2(X0,k1_zfmisc_1(X1)) = X1 | r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u82,axiom,
% 0.20/0.51      ~r1_tarski(X0,sK2(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = k4_xboole_0(sK2(X1,k1_zfmisc_1(X0)),X1) | sK2(X1,k1_zfmisc_1(X0)) = X0 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u69,axiom,
% 0.20/0.51      ~r1_tarski(X0,sK2(X0,k1_zfmisc_1(X1))) | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) | sK2(X0,k1_zfmisc_1(X1)) = X0 | r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u85,axiom,
% 0.20/0.51      ~r1_tarski(X1,sK2(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = k4_xboole_0(sK2(X1,k1_zfmisc_1(X0)),X0) | sK2(X1,k1_zfmisc_1(X0)) = X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u50,axiom,
% 0.20/0.51      ~r1_tarski(X3,X0) | r2_hidden(X3,k1_zfmisc_1(X0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u46,axiom,
% 0.20/0.51      ~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0).
% 0.20/0.51  
% 0.20/0.51  cnf(u40,axiom,
% 0.20/0.51      ~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u61,negated_conjecture,
% 0.20/0.51      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u33,axiom,
% 0.20/0.51      k2_subset_1(X0) = X0).
% 0.20/0.51  
% 0.20/0.51  cnf(u35,axiom,
% 0.20/0.51      k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u83,axiom,
% 0.20/0.51      k1_xboole_0 = k4_xboole_0(sK2(X3,k1_zfmisc_1(X2)),X3) | k1_xboole_0 = k4_xboole_0(sK2(X3,k1_zfmisc_1(X2)),X2) | k1_zfmisc_1(X3) = k1_zfmisc_1(X2)).
% 0.20/0.51  
% 0.20/0.51  % (12935)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  cnf(u83,axiom,
% 0.20/0.51      k1_xboole_0 = k4_xboole_0(sK2(X3,k1_zfmisc_1(X2)),X3) | k1_xboole_0 = k4_xboole_0(sK2(X3,k1_zfmisc_1(X2)),X2) | k1_zfmisc_1(X3) = k1_zfmisc_1(X2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u77,negated_conjecture,
% 0.20/0.51      k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u59,axiom,
% 0.20/0.51      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u31,negated_conjecture,
% 0.20/0.51      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u62,axiom,
% 0.20/0.51      k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u36,axiom,
% 0.20/0.51      k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u45,axiom,
% 0.20/0.51      k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u28,negated_conjecture,
% 0.20/0.51      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 != k2_struct_0(sK0)).
% 0.20/0.51  
% 0.20/0.51  % (12938)# SZS output end Saturation.
% 0.20/0.51  % (12938)------------------------------
% 0.20/0.51  % (12938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (12938)Termination reason: Satisfiable
% 0.20/0.51  
% 0.20/0.51  % (12938)Memory used [KB]: 1791
% 0.20/0.51  % (12938)Time elapsed: 0.106 s
% 0.20/0.51  % (12938)------------------------------
% 0.20/0.51  % (12938)------------------------------
% 0.20/0.51  % (12930)Success in time 0.158 s
%------------------------------------------------------------------------------
