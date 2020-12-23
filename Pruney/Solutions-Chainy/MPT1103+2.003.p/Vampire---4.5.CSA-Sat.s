%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:34 EST 2020

% Result     : CounterSatisfiable 1.11s
% Output     : Saturation 1.58s
% Verified   : 
% Statistics : Number of clauses        :   30 (  30 expanded)
%              Number of leaves         :   30 (  30 expanded)
%              Depth                    :    0
%              Number of atoms          :   37 (  37 expanded)
%              Number of equality atoms :   30 (  30 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u21,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u27,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u41,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u116,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u57,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u43,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) )).

cnf(u35,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

cnf(u119,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u117,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u118,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u90,axiom,
    ( k7_subset_1(X1,X1,X2) = k7_subset_1(k2_xboole_0(X2,X1),k2_xboole_0(X2,X1),X2) )).

cnf(u79,axiom,
    ( k7_subset_1(X2,X2,X3) = k7_subset_1(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3),X3) )).

cnf(u59,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u86,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u65,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1) )).

cnf(u18,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u58,axiom,
    ( k5_xboole_0(k2_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X1,k2_xboole_0(X0,X1)))) = k7_subset_1(X0,X0,X1) )).

cnf(u56,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u28,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u75,axiom,
    ( k7_subset_1(X1,X1,X2) = k5_xboole_0(k2_xboole_0(X2,X1),k1_setfam_1(k2_tarski(X2,k2_xboole_0(X2,X1)))) )).

cnf(u81,axiom,
    ( k1_xboole_0 = k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X5))) )).

cnf(u60,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) )).

cnf(u29,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

cnf(u64,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u22,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u40,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u47,axiom,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 )).

cnf(u24,axiom,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u39,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n012.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:30:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.37  ipcrm: permission denied for id (812154880)
% 0.15/0.37  ipcrm: permission denied for id (812220418)
% 0.15/0.37  ipcrm: permission denied for id (812253188)
% 0.15/0.38  ipcrm: permission denied for id (812351495)
% 0.15/0.38  ipcrm: permission denied for id (812417034)
% 0.15/0.38  ipcrm: permission denied for id (812449803)
% 0.15/0.38  ipcrm: permission denied for id (812482572)
% 0.15/0.38  ipcrm: permission denied for id (812515341)
% 0.15/0.38  ipcrm: permission denied for id (812548111)
% 0.15/0.39  ipcrm: permission denied for id (812646418)
% 0.15/0.39  ipcrm: permission denied for id (812679187)
% 0.15/0.39  ipcrm: permission denied for id (812711956)
% 0.15/0.40  ipcrm: permission denied for id (812875801)
% 0.15/0.40  ipcrm: permission denied for id (812908570)
% 0.15/0.40  ipcrm: permission denied for id (812941339)
% 0.15/0.40  ipcrm: permission denied for id (813039647)
% 0.21/0.41  ipcrm: permission denied for id (813137954)
% 0.21/0.41  ipcrm: permission denied for id (813269030)
% 0.21/0.41  ipcrm: permission denied for id (813301799)
% 0.21/0.42  ipcrm: permission denied for id (813334568)
% 0.21/0.42  ipcrm: permission denied for id (813367337)
% 0.21/0.42  ipcrm: permission denied for id (813400106)
% 0.21/0.42  ipcrm: permission denied for id (813465644)
% 0.21/0.43  ipcrm: permission denied for id (813662257)
% 0.21/0.43  ipcrm: permission denied for id (813695026)
% 0.21/0.43  ipcrm: permission denied for id (813727795)
% 0.21/0.43  ipcrm: permission denied for id (813760564)
% 0.21/0.43  ipcrm: permission denied for id (813826102)
% 0.21/0.44  ipcrm: permission denied for id (813891641)
% 0.21/0.44  ipcrm: permission denied for id (813924410)
% 0.21/0.44  ipcrm: permission denied for id (813957179)
% 0.21/0.44  ipcrm: permission denied for id (813989948)
% 0.21/0.44  ipcrm: permission denied for id (814022717)
% 0.21/0.44  ipcrm: permission denied for id (814055486)
% 0.21/0.44  ipcrm: permission denied for id (814088255)
% 0.21/0.44  ipcrm: permission denied for id (814121024)
% 0.21/0.45  ipcrm: permission denied for id (814153793)
% 0.21/0.45  ipcrm: permission denied for id (814186562)
% 0.21/0.45  ipcrm: permission denied for id (814284869)
% 0.21/0.45  ipcrm: permission denied for id (814350407)
% 0.21/0.46  ipcrm: permission denied for id (814383176)
% 0.21/0.46  ipcrm: permission denied for id (814415945)
% 0.21/0.46  ipcrm: permission denied for id (814547021)
% 0.21/0.46  ipcrm: permission denied for id (814579790)
% 0.21/0.47  ipcrm: permission denied for id (814612559)
% 0.21/0.47  ipcrm: permission denied for id (814645328)
% 0.21/0.47  ipcrm: permission denied for id (814743635)
% 0.21/0.47  ipcrm: permission denied for id (814776404)
% 0.21/0.48  ipcrm: permission denied for id (814940249)
% 0.21/0.48  ipcrm: permission denied for id (814973018)
% 0.21/0.48  ipcrm: permission denied for id (815005787)
% 0.21/0.49  ipcrm: permission denied for id (815038556)
% 0.21/0.49  ipcrm: permission denied for id (815071325)
% 0.21/0.49  ipcrm: permission denied for id (815202401)
% 0.21/0.50  ipcrm: permission denied for id (815267939)
% 0.21/0.50  ipcrm: permission denied for id (815333477)
% 0.21/0.50  ipcrm: permission denied for id (815399015)
% 0.21/0.51  ipcrm: permission denied for id (815497322)
% 0.21/0.51  ipcrm: permission denied for id (815595629)
% 0.21/0.51  ipcrm: permission denied for id (815726703)
% 0.21/0.52  ipcrm: permission denied for id (815759472)
% 0.21/0.52  ipcrm: permission denied for id (815825011)
% 0.21/0.52  ipcrm: permission denied for id (815857780)
% 0.21/0.52  ipcrm: permission denied for id (815890549)
% 0.21/0.53  ipcrm: permission denied for id (815923318)
% 0.21/0.53  ipcrm: permission denied for id (816054394)
% 0.21/0.54  ipcrm: permission denied for id (816119933)
% 0.21/0.54  ipcrm: permission denied for id (816185471)
% 1.11/0.71  % (17559)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.11/0.72  % SZS status CounterSatisfiable for theBenchmark
% 1.58/0.73  % (17575)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.58/0.73  % (17567)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.58/0.73  % (17575)Refutation not found, incomplete strategy% (17575)------------------------------
% 1.58/0.73  % (17575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.73  % (17578)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.58/0.73  % (17559)# SZS output start Saturation.
% 1.58/0.73  cnf(u21,negated_conjecture,
% 1.58/0.73      l1_struct_0(sK0)).
% 1.58/0.73  
% 1.58/0.73  cnf(u27,axiom,
% 1.58/0.73      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 1.58/0.73  
% 1.58/0.73  cnf(u41,axiom,
% 1.58/0.73      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.58/0.73  
% 1.58/0.73  cnf(u20,negated_conjecture,
% 1.58/0.73      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.58/0.73  
% 1.58/0.73  cnf(u116,negated_conjecture,
% 1.58/0.73      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 1.58/0.73  
% 1.58/0.73  cnf(u57,axiom,
% 1.58/0.73      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 1.58/0.73  
% 1.58/0.73  cnf(u43,axiom,
% 1.58/0.73      k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))).
% 1.58/0.73  
% 1.58/0.73  cnf(u35,axiom,
% 1.58/0.73      k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))).
% 1.58/0.73  
% 1.58/0.73  cnf(u119,negated_conjecture,
% 1.58/0.73      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 1.58/0.73  
% 1.58/0.73  cnf(u117,negated_conjecture,
% 1.58/0.73      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 1.58/0.73  
% 1.58/0.73  cnf(u118,negated_conjecture,
% 1.58/0.73      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 1.58/0.73  
% 1.58/0.73  cnf(u90,axiom,
% 1.58/0.73      k7_subset_1(X1,X1,X2) = k7_subset_1(k2_xboole_0(X2,X1),k2_xboole_0(X2,X1),X2)).
% 1.58/0.73  
% 1.58/0.73  cnf(u79,axiom,
% 1.58/0.73      k7_subset_1(X2,X2,X3) = k7_subset_1(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3),X3)).
% 1.58/0.73  
% 1.58/0.73  cnf(u59,negated_conjecture,
% 1.58/0.73      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 1.58/0.73  
% 1.58/0.73  cnf(u86,axiom,
% 1.58/0.73      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 1.58/0.73  
% 1.58/0.73  cnf(u65,axiom,
% 1.58/0.73      k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1)).
% 1.58/0.73  
% 1.58/0.73  cnf(u18,negated_conjecture,
% 1.58/0.73      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 1.58/0.73  
% 1.58/0.73  cnf(u58,axiom,
% 1.58/0.73      k5_xboole_0(k2_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X1,k2_xboole_0(X0,X1)))) = k7_subset_1(X0,X0,X1)).
% 1.58/0.73  
% 1.58/0.73  cnf(u56,axiom,
% 1.58/0.73      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 1.58/0.73  
% 1.58/0.73  cnf(u28,axiom,
% 1.58/0.73      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 1.58/0.73  
% 1.58/0.73  cnf(u75,axiom,
% 1.58/0.73      k7_subset_1(X1,X1,X2) = k5_xboole_0(k2_xboole_0(X2,X1),k1_setfam_1(k2_tarski(X2,k2_xboole_0(X2,X1))))).
% 1.58/0.73  
% 1.58/0.73  cnf(u81,axiom,
% 1.58/0.73      k1_xboole_0 = k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X5)))).
% 1.58/0.73  
% 1.58/0.73  cnf(u60,axiom,
% 1.58/0.73      k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))).
% 1.58/0.73  
% 1.58/0.73  cnf(u29,axiom,
% 1.58/0.73      k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)).
% 1.58/0.73  
% 1.58/0.73  cnf(u64,axiom,
% 1.58/0.73      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 1.58/0.73  
% 1.58/0.73  cnf(u22,axiom,
% 1.58/0.73      k2_subset_1(X0) = X0).
% 1.58/0.73  
% 1.58/0.73  cnf(u40,axiom,
% 1.58/0.73      k5_xboole_0(X0,k1_xboole_0) = X0).
% 1.58/0.73  
% 1.58/0.73  cnf(u47,axiom,
% 1.58/0.73      k2_xboole_0(k1_xboole_0,X0) = X0).
% 1.58/0.73  
% 1.58/0.73  cnf(u24,axiom,
% 1.58/0.73      k2_xboole_0(X0,k1_xboole_0) = X0).
% 1.58/0.73  
% 1.58/0.73  cnf(u39,negated_conjecture,
% 1.58/0.73      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.58/0.73  
% 1.58/0.73  % (17559)# SZS output end Saturation.
% 1.58/0.73  % (17559)------------------------------
% 1.58/0.73  % (17559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.73  % (17559)Termination reason: Satisfiable
% 1.58/0.73  
% 1.58/0.73  % (17559)Memory used [KB]: 6268
% 1.58/0.73  % (17559)Time elapsed: 0.097 s
% 1.58/0.73  % (17559)------------------------------
% 1.58/0.73  % (17559)------------------------------
% 1.58/0.73  % (17383)Success in time 0.367 s
%------------------------------------------------------------------------------
