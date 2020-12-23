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
% DateTime   : Thu Dec  3 13:08:30 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   55 (  55 expanded)
%              Number of leaves         :   55 (  55 expanded)
%              Depth                    :    0
%              Number of atoms          :   72 (  72 expanded)
%              Number of equality atoms :   44 (  44 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u66,axiom,
    ( m1_subset_1(k3_subset_1(X5,X5),k1_zfmisc_1(X5)) )).

cnf(u41,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u44,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u58,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u57,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_xboole_0(X0,sK1) = k7_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u89,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X0) = k3_xboole_0(X1,k3_subset_1(X0,X0)) )).

cnf(u88,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_xboole_0(X1,X0) = k7_subset_1(X0,X1,k3_subset_1(X0,X0)) )).

cnf(u37,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) )).

cnf(u35,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u31,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )).

cnf(u30,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u29,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) )).

cnf(u84,axiom,
    ( r1_tarski(k3_subset_1(X6,X6),X6) )).

cnf(u55,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) )).

cnf(u40,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u38,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u69,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),sK1) )).

cnf(u45,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) )).

cnf(u116,axiom,
    ( ~ r1_tarski(X0,k3_subset_1(X0,X0))
    | k3_subset_1(X0,X0) = X0 )).

cnf(u36,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u28,axiom,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 )).

cnf(u34,axiom,
    ( ~ r1_tarski(X1,X0)
    | X0 = X1
    | ~ r1_tarski(X0,X1) )).

cnf(u123,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u79,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u75,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u46,negated_conjecture,
    ( sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u48,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u126,axiom,
    ( k7_subset_1(X0,X0,k3_subset_1(X0,X0)) = X0 )).

cnf(u107,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK1) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) )).

cnf(u96,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u77,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u60,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u81,axiom,
    ( k9_subset_1(X2,X3,k3_subset_1(X2,X2)) = k3_xboole_0(X3,k3_subset_1(X2,X2)) )).

cnf(u52,negated_conjecture,
    ( k9_subset_1(u1_struct_0(sK0),X1,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_xboole_0(X1,k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u49,negated_conjecture,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1) )).

cnf(u129,axiom,
    ( k3_subset_1(X1,X1) = k3_xboole_0(X1,k3_subset_1(X1,X1)) )).

cnf(u117,axiom,
    ( k3_subset_1(X1,X1) = k3_xboole_0(k3_subset_1(X1,X1),X1) )).

cnf(u98,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k3_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u70,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k3_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) )).

cnf(u65,axiom,
    ( k3_subset_1(X4,k3_subset_1(X4,X4)) = X4 )).

cnf(u134,axiom,
    ( k3_subset_1(X1,X1) = k7_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(X1,X1)) )).

cnf(u133,axiom,
    ( k3_subset_1(X0,X0) = k7_subset_1(X0,X0,X0) )).

cnf(u97,axiom,
    ( k3_subset_1(X1,X1) = k7_subset_1(X1,k3_subset_1(X1,X1),X1) )).

cnf(u125,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u102,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

cnf(u62,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) )).

cnf(u108,negated_conjecture,
    ( k3_xboole_0(k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) )).

cnf(u93,negated_conjecture,
    ( k3_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) )).

cnf(u92,negated_conjecture,
    ( k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) = k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u42,axiom,
    ( k3_xboole_0(X0,X0) = X0 )).

cnf(u64,axiom,
    ( k3_xboole_0(X3,X2) = k9_subset_1(X2,X3,X2) )).

cnf(u27,axiom,
    ( k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) )).

cnf(u26,axiom,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

cnf(u25,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (7634)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.50  % (7627)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.50  % (7653)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (7656)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (7640)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (7645)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.51  % (7639)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.51  % (7634)# SZS output start Saturation.
% 0.20/0.51  cnf(u66,axiom,
% 0.20/0.51      m1_subset_1(k3_subset_1(X5,X5),k1_zfmisc_1(X5))).
% 0.20/0.51  
% 0.20/0.51  cnf(u41,axiom,
% 0.20/0.51      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u44,negated_conjecture,
% 0.20/0.51      m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u24,negated_conjecture,
% 0.20/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u58,negated_conjecture,
% 0.20/0.51      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u57,negated_conjecture,
% 0.20/0.51      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_xboole_0(X0,sK1) = k7_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u89,axiom,
% 0.20/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X0) = k3_xboole_0(X1,k3_subset_1(X0,X0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u88,axiom,
% 0.20/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_xboole_0(X1,X0) = k7_subset_1(X0,X1,k3_subset_1(X0,X0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u37,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u35,axiom,
% 0.20/0.51      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u31,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u30,axiom,
% 0.20/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.20/0.51  
% 0.20/0.51  cnf(u29,axiom,
% 0.20/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u84,axiom,
% 0.20/0.51      r1_tarski(k3_subset_1(X6,X6),X6)).
% 0.20/0.51  
% 0.20/0.51  cnf(u55,negated_conjecture,
% 0.20/0.51      r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u40,negated_conjecture,
% 0.20/0.51      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u38,axiom,
% 0.20/0.51      r1_tarski(X1,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u69,negated_conjecture,
% 0.20/0.51      ~r1_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u45,negated_conjecture,
% 0.20/0.51      ~r1_tarski(u1_struct_0(sK0),sK1) | sK1 = u1_struct_0(sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u116,axiom,
% 0.20/0.51      ~r1_tarski(X0,k3_subset_1(X0,X0)) | k3_subset_1(X0,X0) = X0).
% 0.20/0.51  
% 0.20/0.51  cnf(u36,axiom,
% 0.20/0.51      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u28,axiom,
% 0.20/0.51      ~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0).
% 0.20/0.51  
% 0.20/0.51  cnf(u34,axiom,
% 0.20/0.51      ~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u123,negated_conjecture,
% 0.20/0.51      sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u79,negated_conjecture,
% 0.20/0.51      sK1 = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u75,negated_conjecture,
% 0.20/0.51      sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u46,negated_conjecture,
% 0.20/0.51      sK1 = k3_xboole_0(sK1,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u48,negated_conjecture,
% 0.20/0.51      sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u126,axiom,
% 0.20/0.51      k7_subset_1(X0,X0,k3_subset_1(X0,X0)) = X0).
% 0.20/0.51  
% 0.20/0.51  cnf(u107,negated_conjecture,
% 0.20/0.51      k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),sK1) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u96,negated_conjecture,
% 0.20/0.51      k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u77,negated_conjecture,
% 0.20/0.51      k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u60,negated_conjecture,
% 0.20/0.51      k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u81,axiom,
% 0.20/0.51      k9_subset_1(X2,X3,k3_subset_1(X2,X2)) = k3_xboole_0(X3,k3_subset_1(X2,X2))).
% 0.20/0.51  
% 0.20/0.51  cnf(u52,negated_conjecture,
% 0.20/0.51      k9_subset_1(u1_struct_0(sK0),X1,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_xboole_0(X1,k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u49,negated_conjecture,
% 0.20/0.51      k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u129,axiom,
% 0.20/0.51      k3_subset_1(X1,X1) = k3_xboole_0(X1,k3_subset_1(X1,X1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u117,axiom,
% 0.20/0.51      k3_subset_1(X1,X1) = k3_xboole_0(k3_subset_1(X1,X1),X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u98,negated_conjecture,
% 0.20/0.51      k3_subset_1(u1_struct_0(sK0),sK1) = k3_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u70,negated_conjecture,
% 0.20/0.51      k3_subset_1(u1_struct_0(sK0),sK1) = k3_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u65,axiom,
% 0.20/0.51      k3_subset_1(X4,k3_subset_1(X4,X4)) = X4).
% 0.20/0.51  
% 0.20/0.51  cnf(u134,axiom,
% 0.20/0.51      k3_subset_1(X1,X1) = k7_subset_1(X1,k3_subset_1(X1,X1),k3_subset_1(X1,X1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u133,axiom,
% 0.20/0.51      k3_subset_1(X0,X0) = k7_subset_1(X0,X0,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u97,axiom,
% 0.20/0.51      k3_subset_1(X1,X1) = k7_subset_1(X1,k3_subset_1(X1,X1),X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u125,negated_conjecture,
% 0.20/0.51      k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u102,negated_conjecture,
% 0.20/0.51      k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u62,negated_conjecture,
% 0.20/0.51      k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)).
% 0.20/0.51  
% 0.20/0.52  cnf(u108,negated_conjecture,
% 0.20/0.52      k3_xboole_0(k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))).
% 0.20/0.52  
% 0.20/0.52  cnf(u93,negated_conjecture,
% 0.20/0.52      k3_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))).
% 0.20/0.52  
% 0.20/0.52  cnf(u92,negated_conjecture,
% 0.20/0.52      k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) = k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 0.20/0.52  
% 0.20/0.52  cnf(u42,axiom,
% 0.20/0.52      k3_xboole_0(X0,X0) = X0).
% 0.20/0.52  
% 0.20/0.52  cnf(u64,axiom,
% 0.20/0.52      k3_xboole_0(X3,X2) = k9_subset_1(X2,X3,X2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u27,axiom,
% 0.20/0.52      k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))).
% 0.20/0.52  
% 0.20/0.52  cnf(u26,axiom,
% 0.20/0.52      k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u25,negated_conjecture,
% 0.20/0.52      sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.20/0.52  
% 0.20/0.52  % (7634)# SZS output end Saturation.
% 0.20/0.52  % (7634)------------------------------
% 0.20/0.52  % (7634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (7634)Termination reason: Satisfiable
% 0.20/0.52  
% 0.20/0.52  % (7634)Memory used [KB]: 1791
% 0.20/0.52  % (7634)Time elapsed: 0.108 s
% 0.20/0.52  % (7634)------------------------------
% 0.20/0.52  % (7634)------------------------------
% 0.20/0.52  % (7626)Success in time 0.163 s
%------------------------------------------------------------------------------
