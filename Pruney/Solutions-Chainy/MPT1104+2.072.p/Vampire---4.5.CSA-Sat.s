%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:59 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   51 (  51 expanded)
%              Number of leaves         :   51 (  51 expanded)
%              Depth                    :    0
%              Number of atoms          :   74 (  74 expanded)
%              Number of equality atoms :   40 (  40 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u49,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u26,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u59,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK1) = k2_xboole_0(X0,sK1) )).

cnf(u60,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X1,sK2) = k2_xboole_0(X1,sK2) )).

cnf(u40,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u43,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )).

cnf(u74,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k2_xboole_0(X1,X0) = k4_subset_1(X0,X1,X0) )).

cnf(u48,negated_conjecture,
    ( r1_tarski(sK2,u1_struct_0(sK0)) )).

cnf(u47,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u44,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u63,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),sK2)
    | u1_struct_0(sK0) = sK2 )).

cnf(u61,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) )).

cnf(u41,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u37,axiom,
    ( ~ r1_tarski(X1,X0)
    | X0 = X1
    | ~ r1_tarski(X0,X1) )).

cnf(u46,negated_conjecture,
    ( r1_xboole_0(sK2,sK1) )).

cnf(u29,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u34,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) )).

cnf(u38,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 )).

cnf(u102,negated_conjecture,
    ( sK2 = k4_xboole_0(k2_struct_0(sK0),sK1) )).

cnf(u52,negated_conjecture,
    ( sK2 = k4_xboole_0(sK2,sK1) )).

cnf(u103,negated_conjecture,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u51,negated_conjecture,
    ( sK1 = k4_xboole_0(sK1,sK2) )).

cnf(u72,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

cnf(u73,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u28,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u57,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u80,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u79,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(sK2,u1_struct_0(sK0)) )).

cnf(u71,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) )).

cnf(u67,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) )).

cnf(u75,axiom,
    ( k4_xboole_0(X2,X3) = k7_subset_1(X2,X2,X3) )).

cnf(u58,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X1) = k4_xboole_0(sK2,X1) )).

cnf(u53,axiom,
    ( k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) )).

cnf(u33,axiom,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) )).

cnf(u109,negated_conjecture,
    ( k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u108,negated_conjecture,
    ( k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u110,axiom,
    ( k2_xboole_0(X0,X0) = k4_subset_1(X0,X0,X0) )).

cnf(u32,axiom,
    ( k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) )).

cnf(u31,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

cnf(u107,negated_conjecture,
    ( sK2 != k2_xboole_0(sK1,k2_struct_0(sK0))
    | r1_xboole_0(k2_xboole_0(sK1,k2_struct_0(sK0)),sK1) )).

cnf(u125,negated_conjecture,
    ( sK1 != k2_xboole_0(sK2,k2_struct_0(sK0))
    | r1_xboole_0(k2_xboole_0(sK2,k2_struct_0(sK0)),sK2) )).

cnf(u92,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | r1_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u99,negated_conjecture,
    ( k2_struct_0(sK0) != sK2
    | r1_xboole_0(k2_struct_0(sK0),sK1) )).

cnf(u30,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 )).

cnf(u90,axiom,
    ( k4_xboole_0(X3,X2) != k2_xboole_0(X2,k2_xboole_0(X2,X3))
    | r1_xboole_0(k2_xboole_0(X2,k2_xboole_0(X2,X3)),X2) )).

cnf(u88,axiom,
    ( k4_xboole_0(X0,X1) != k2_xboole_0(X1,k2_xboole_0(X0,X1))
    | r1_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X1)),X1) )).

cnf(u39,axiom,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) )).

cnf(u83,axiom,
    ( k2_xboole_0(X1,X2) != k4_xboole_0(X2,X1)
    | r1_xboole_0(k2_xboole_0(X1,X2),X1) )).

cnf(u55,axiom,
    ( k2_xboole_0(X0,X1) != k4_xboole_0(X0,X1)
    | r1_xboole_0(k2_xboole_0(X0,X1),X1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:05:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (15794)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.46  % (15809)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.46  % (15794)Refutation not found, incomplete strategy% (15794)------------------------------
% 0.21/0.46  % (15794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (15794)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (15794)Memory used [KB]: 1663
% 0.21/0.46  % (15794)Time elapsed: 0.053 s
% 0.21/0.46  % (15794)------------------------------
% 0.21/0.46  % (15794)------------------------------
% 0.21/0.46  % (15809)Refutation not found, incomplete strategy% (15809)------------------------------
% 0.21/0.46  % (15809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (15809)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (15809)Memory used [KB]: 10618
% 0.21/0.46  % (15809)Time elapsed: 0.068 s
% 0.21/0.46  % (15809)------------------------------
% 0.21/0.46  % (15809)------------------------------
% 0.21/0.48  % (15796)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.49  % (15797)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.49  % (15804)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.50  % (15802)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.50  % (15804)Refutation not found, incomplete strategy% (15804)------------------------------
% 0.21/0.50  % (15804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (15804)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (15804)Memory used [KB]: 6268
% 0.21/0.50  % (15804)Time elapsed: 0.094 s
% 0.21/0.50  % (15804)------------------------------
% 0.21/0.50  % (15804)------------------------------
% 0.21/0.50  % (15801)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.50  % (15820)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.50  % (15807)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (15821)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.51  % (15793)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (15812)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.51  % (15800)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (15811)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.51  % (15813)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (15817)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (15822)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (15822)Refutation not found, incomplete strategy% (15822)------------------------------
% 0.21/0.51  % (15822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15822)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15822)Memory used [KB]: 1663
% 0.21/0.51  % (15822)Time elapsed: 0.001 s
% 0.21/0.51  % (15822)------------------------------
% 0.21/0.51  % (15822)------------------------------
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (15800)# SZS output start Saturation.
% 0.21/0.51  cnf(u49,axiom,
% 0.21/0.51      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u27,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u26,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u59,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK1) = k2_xboole_0(X0,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u60,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X1,sK2) = k2_xboole_0(X1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u40,axiom,
% 0.21/0.51      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u42,axiom,
% 0.21/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u43,axiom,
% 0.21/0.51      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u74,axiom,
% 0.21/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X0) = k4_subset_1(X0,X1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u48,negated_conjecture,
% 0.21/0.51      r1_tarski(sK2,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u47,negated_conjecture,
% 0.21/0.51      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u44,axiom,
% 0.21/0.51      r1_tarski(X1,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u63,negated_conjecture,
% 0.21/0.51      ~r1_tarski(u1_struct_0(sK0),sK2) | u1_struct_0(sK0) = sK2).
% 0.21/0.51  
% 0.21/0.51  cnf(u61,negated_conjecture,
% 0.21/0.51      ~r1_tarski(u1_struct_0(sK0),sK1) | sK1 = u1_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u41,axiom,
% 0.21/0.51      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 0.21/0.51  
% 0.21/0.51  cnf(u37,axiom,
% 0.21/0.51      ~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u46,negated_conjecture,
% 0.21/0.51      r1_xboole_0(sK2,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u29,negated_conjecture,
% 0.21/0.51      r1_xboole_0(sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u34,axiom,
% 0.21/0.51      ~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u38,axiom,
% 0.21/0.51      ~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0).
% 0.21/0.51  
% 0.21/0.51  cnf(u102,negated_conjecture,
% 0.21/0.51      sK2 = k4_xboole_0(k2_struct_0(sK0),sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u52,negated_conjecture,
% 0.21/0.51      sK2 = k4_xboole_0(sK2,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u103,negated_conjecture,
% 0.21/0.51      sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u51,negated_conjecture,
% 0.21/0.51      sK1 = k4_xboole_0(sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u72,negated_conjecture,
% 0.21/0.51      k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u73,negated_conjecture,
% 0.21/0.51      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u28,negated_conjecture,
% 0.21/0.51      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u57,negated_conjecture,
% 0.21/0.51      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u80,negated_conjecture,
% 0.21/0.51      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(sK1,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u79,negated_conjecture,
% 0.21/0.51      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(sK2,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u71,negated_conjecture,
% 0.21/0.51      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u67,negated_conjecture,
% 0.21/0.51      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u75,axiom,
% 0.21/0.51      k4_xboole_0(X2,X3) = k7_subset_1(X2,X2,X3)).
% 0.21/0.51  
% 0.21/0.51  cnf(u58,negated_conjecture,
% 0.21/0.51      k7_subset_1(u1_struct_0(sK0),sK2,X1) = k4_xboole_0(sK2,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u53,axiom,
% 0.21/0.51      k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u33,axiom,
% 0.21/0.51      k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u109,negated_conjecture,
% 0.21/0.51      k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u108,negated_conjecture,
% 0.21/0.51      k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u110,axiom,
% 0.21/0.51      k2_xboole_0(X0,X0) = k4_subset_1(X0,X0,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u32,axiom,
% 0.21/0.51      k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))).
% 0.21/0.51  
% 0.21/0.51  cnf(u31,axiom,
% 0.21/0.51      k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u107,negated_conjecture,
% 0.21/0.51      sK2 != k2_xboole_0(sK1,k2_struct_0(sK0)) | r1_xboole_0(k2_xboole_0(sK1,k2_struct_0(sK0)),sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u125,negated_conjecture,
% 0.21/0.51      sK1 != k2_xboole_0(sK2,k2_struct_0(sK0)) | r1_xboole_0(k2_xboole_0(sK2,k2_struct_0(sK0)),sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u92,negated_conjecture,
% 0.21/0.51      sK1 != k2_struct_0(sK0) | r1_xboole_0(k2_struct_0(sK0),sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u99,negated_conjecture,
% 0.21/0.51      k2_struct_0(sK0) != sK2 | r1_xboole_0(k2_struct_0(sK0),sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u30,negated_conjecture,
% 0.21/0.51      k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2).
% 0.21/0.51  
% 0.21/0.51  cnf(u90,axiom,
% 0.21/0.51      k4_xboole_0(X3,X2) != k2_xboole_0(X2,k2_xboole_0(X2,X3)) | r1_xboole_0(k2_xboole_0(X2,k2_xboole_0(X2,X3)),X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u88,axiom,
% 0.21/0.51      k4_xboole_0(X0,X1) != k2_xboole_0(X1,k2_xboole_0(X0,X1)) | r1_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X1)),X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u39,axiom,
% 0.21/0.51      k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u83,axiom,
% 0.21/0.51      k2_xboole_0(X1,X2) != k4_xboole_0(X2,X1) | r1_xboole_0(k2_xboole_0(X1,X2),X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u55,axiom,
% 0.21/0.51      k2_xboole_0(X0,X1) != k4_xboole_0(X0,X1) | r1_xboole_0(k2_xboole_0(X0,X1),X1)).
% 0.21/0.51  
% 0.21/0.51  % (15800)# SZS output end Saturation.
% 0.21/0.51  % (15800)------------------------------
% 0.21/0.51  % (15800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15800)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (15800)Memory used [KB]: 1791
% 0.21/0.51  % (15800)Time elapsed: 0.103 s
% 0.21/0.51  % (15800)------------------------------
% 0.21/0.51  % (15800)------------------------------
% 0.21/0.51  % (15792)Success in time 0.149 s
%------------------------------------------------------------------------------
