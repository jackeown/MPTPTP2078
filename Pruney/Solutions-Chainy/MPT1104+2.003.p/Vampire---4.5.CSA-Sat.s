%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:50 EST 2020

% Result     : CounterSatisfiable 1.55s
% Output     : Saturation 1.55s
% Verified   : 
% Statistics : Number of clauses        :   70 (  70 expanded)
%              Number of leaves         :   70 (  70 expanded)
%              Depth                    :    0
%              Number of atoms          :   77 (  77 expanded)
%              Number of equality atoms :   66 (  66 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u52,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u28,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u125,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)) )).

cnf(u126,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k5_xboole_0(X1,k7_subset_1(sK1,sK1,X1)) )).

cnf(u63,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u62,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k7_subset_1(X2,X2,X1)) )).

cnf(u127,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | k5_xboole_0(X2,k7_subset_1(X3,X3,X2)) = k4_subset_1(X3,X2,X3) )).

cnf(u26,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u48,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) )).

cnf(u58,negated_conjecture,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,sK2)) )).

cnf(u54,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) )).

cnf(u44,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

cnf(u170,negated_conjecture,
    ( sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) )).

cnf(u88,negated_conjecture,
    ( sK2 = k7_subset_1(sK2,sK2,sK1) )).

cnf(u183,negated_conjecture,
    ( sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) )).

cnf(u77,negated_conjecture,
    ( sK1 = k7_subset_1(sK1,sK1,sK2) )).

cnf(u306,negated_conjecture,
    ( k7_subset_1(sK2,sK2,u1_struct_0(sK0)) = k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_struct_0(sK0)) )).

cnf(u323,negated_conjecture,
    ( k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) )).

cnf(u290,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) )).

cnf(u274,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),sK2) )).

cnf(u67,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) )).

cnf(u66,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1) )).

cnf(u244,axiom,
    ( k7_subset_1(X4,X4,X3) = k7_subset_1(k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),X3) )).

cnf(u154,axiom,
    ( k7_subset_1(X2,X2,X3) = k7_subset_1(k5_xboole_0(X2,k7_subset_1(X3,X3,X2)),k5_xboole_0(X2,k7_subset_1(X3,X3,X2)),X3) )).

cnf(u61,axiom,
    ( k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))) )).

cnf(u279,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK2,sK2,k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) )).

cnf(u187,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK2,sK2,k2_struct_0(sK0)) )).

cnf(u295,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) )).

cnf(u174,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) )).

cnf(u329,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) )).

cnf(u312,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) )).

cnf(u491,axiom,
    ( k1_xboole_0 = k7_subset_1(k5_xboole_0(X4,k7_subset_1(X3,X3,X4)),k5_xboole_0(X4,k7_subset_1(X3,X3,X4)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3))) )).

cnf(u76,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1) )).

cnf(u464,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) )).

cnf(u442,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))) )).

cnf(u198,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u208,negated_conjecture,
    ( sK2 = k4_subset_1(u1_struct_0(sK0),sK2,sK2) )).

cnf(u207,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) )).

cnf(u142,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u25,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u225,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u221,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u228,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u224,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u219,negated_conjecture,
    ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u218,negated_conjecture,
    ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u33,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u162,negated_conjecture,
    ( sK2 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))) )).

cnf(u164,negated_conjecture,
    ( sK1 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))) )).

cnf(u133,negated_conjecture,
    ( k2_struct_0(sK0) = k5_xboole_0(sK2,sK1) )).

cnf(u132,negated_conjecture,
    ( k2_struct_0(sK0) = k5_xboole_0(sK1,sK2) )).

cnf(u222,negated_conjecture,
    ( k7_subset_1(sK2,sK2,u1_struct_0(sK0)) = k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))))) )).

cnf(u226,negated_conjecture,
    ( k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))))) )).

cnf(u227,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))))) )).

cnf(u223,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))))) )).

cnf(u147,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))))) )).

cnf(u68,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(X1,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) )).

cnf(u70,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) )).

cnf(u771,axiom,
    ( k5_xboole_0(X3,k7_subset_1(X4,X4,X3)) = k5_xboole_0(k5_xboole_0(X4,k7_subset_1(X3,X3,X4)),k1_xboole_0) )).

cnf(u69,axiom,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) )).

cnf(u948,axiom,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(X4,k7_subset_1(X5,X5,X4)),k1_setfam_1(k2_tarski(k5_xboole_0(X4,k7_subset_1(X5,X5,X4)),k5_xboole_0(X5,k7_subset_1(X4,X4,X5))))) )).

cnf(u490,axiom,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(X4,k7_subset_1(X3,X3,X4)),k1_setfam_1(k2_tarski(k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X4,k7_subset_1(X3,X3,X4))))) )).

cnf(u157,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) )).

cnf(u75,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u230,axiom,
    ( k4_subset_1(X0,X0,X0) = X0 )).

cnf(u29,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u96,axiom,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 )).

cnf(u51,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u27,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (14436)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.49  % (14435)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (14461)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (14462)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (14442)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (14453)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (14432)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (14442)Refutation not found, incomplete strategy% (14442)------------------------------
% 0.20/0.51  % (14442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (14442)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (14442)Memory used [KB]: 10746
% 0.20/0.51  % (14442)Time elapsed: 0.119 s
% 0.20/0.51  % (14442)------------------------------
% 0.20/0.51  % (14442)------------------------------
% 0.20/0.51  % (14440)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (14441)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (14453)Refutation not found, incomplete strategy% (14453)------------------------------
% 0.20/0.51  % (14453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (14440)Refutation not found, incomplete strategy% (14440)------------------------------
% 0.20/0.52  % (14440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (14440)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (14440)Memory used [KB]: 10746
% 0.20/0.52  % (14440)Time elapsed: 0.116 s
% 0.20/0.52  % (14440)------------------------------
% 0.20/0.52  % (14440)------------------------------
% 0.20/0.52  % (14453)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (14453)Memory used [KB]: 10746
% 0.20/0.52  % (14453)Time elapsed: 0.119 s
% 0.20/0.52  % (14453)------------------------------
% 0.20/0.52  % (14453)------------------------------
% 0.20/0.52  % (14454)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (14452)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (14443)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (14455)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (14455)Refutation not found, incomplete strategy% (14455)------------------------------
% 0.20/0.52  % (14455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (14446)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (14437)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (14455)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (14455)Memory used [KB]: 10746
% 0.20/0.52  % (14455)Time elapsed: 0.069 s
% 0.20/0.52  % (14455)------------------------------
% 0.20/0.52  % (14455)------------------------------
% 0.20/0.53  % (14445)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (14431)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (14431)Refutation not found, incomplete strategy% (14431)------------------------------
% 0.20/0.53  % (14431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (14431)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (14431)Memory used [KB]: 1791
% 0.20/0.53  % (14431)Time elapsed: 0.127 s
% 0.20/0.53  % (14431)------------------------------
% 0.20/0.53  % (14431)------------------------------
% 0.20/0.53  % (14460)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.53  % (14434)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.34/0.53  % (14433)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.34/0.53  % (14447)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.34/0.53  % (14447)Refutation not found, incomplete strategy% (14447)------------------------------
% 1.34/0.53  % (14447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (14447)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (14447)Memory used [KB]: 6140
% 1.34/0.53  % (14447)Time elapsed: 0.002 s
% 1.34/0.53  % (14447)------------------------------
% 1.34/0.53  % (14447)------------------------------
% 1.34/0.53  % (14436)Refutation not found, incomplete strategy% (14436)------------------------------
% 1.34/0.53  % (14436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (14436)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (14436)Memory used [KB]: 6652
% 1.34/0.53  % (14436)Time elapsed: 0.138 s
% 1.34/0.53  % (14436)------------------------------
% 1.34/0.53  % (14436)------------------------------
% 1.34/0.53  % (14435)Refutation not found, incomplete strategy% (14435)------------------------------
% 1.34/0.53  % (14435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (14456)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.34/0.54  % (14441)Refutation not found, incomplete strategy% (14441)------------------------------
% 1.34/0.54  % (14441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (14441)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (14441)Memory used [KB]: 10618
% 1.34/0.54  % (14441)Time elapsed: 0.135 s
% 1.34/0.54  % (14441)------------------------------
% 1.34/0.54  % (14441)------------------------------
% 1.34/0.54  % (14456)Refutation not found, incomplete strategy% (14456)------------------------------
% 1.34/0.54  % (14456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (14456)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (14456)Memory used [KB]: 1791
% 1.34/0.54  % (14456)Time elapsed: 0.140 s
% 1.34/0.54  % (14456)------------------------------
% 1.34/0.54  % (14456)------------------------------
% 1.34/0.54  % (14458)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.34/0.54  % (14459)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.54  % (14438)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.34/0.54  % (14457)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.34/0.54  % (14454)Refutation not found, incomplete strategy% (14454)------------------------------
% 1.34/0.54  % (14454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (14454)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (14454)Memory used [KB]: 2046
% 1.34/0.54  % (14454)Time elapsed: 0.160 s
% 1.34/0.54  % (14454)------------------------------
% 1.34/0.54  % (14454)------------------------------
% 1.34/0.54  % (14451)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.54  % (14450)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.55  % (14450)Refutation not found, incomplete strategy% (14450)------------------------------
% 1.34/0.55  % (14450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.55  % (14433)Refutation not found, incomplete strategy% (14433)------------------------------
% 1.55/0.55  % (14433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.55  % (14450)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.55  
% 1.55/0.55  % (14450)Memory used [KB]: 10618
% 1.55/0.55  % (14450)Time elapsed: 0.152 s
% 1.55/0.55  % (14450)------------------------------
% 1.55/0.55  % (14450)------------------------------
% 1.55/0.55  % (14439)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.55/0.55  % (14435)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.55  
% 1.55/0.55  % (14435)Memory used [KB]: 6780
% 1.55/0.55  % (14435)Time elapsed: 0.117 s
% 1.55/0.55  % (14435)------------------------------
% 1.55/0.55  % (14435)------------------------------
% 1.55/0.55  % (14448)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.55/0.56  % (14433)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (14433)Memory used [KB]: 11001
% 1.55/0.56  % (14433)Time elapsed: 0.146 s
% 1.55/0.56  % (14433)------------------------------
% 1.55/0.56  % (14433)------------------------------
% 1.55/0.56  % (14458)Refutation not found, incomplete strategy% (14458)------------------------------
% 1.55/0.56  % (14458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (14438)Refutation not found, incomplete strategy% (14438)------------------------------
% 1.55/0.57  % (14438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (14438)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (14438)Memory used [KB]: 6524
% 1.55/0.57  % (14438)Time elapsed: 0.171 s
% 1.55/0.57  % (14438)------------------------------
% 1.55/0.57  % (14438)------------------------------
% 1.55/0.57  % (14443)Refutation not found, incomplete strategy% (14443)------------------------------
% 1.55/0.57  % (14443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (14458)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (14458)Memory used [KB]: 6908
% 1.55/0.58  % (14458)Time elapsed: 0.154 s
% 1.55/0.58  % (14458)------------------------------
% 1.55/0.58  % (14458)------------------------------
% 1.55/0.58  % (14443)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (14443)Memory used [KB]: 6780
% 1.55/0.58  % (14443)Time elapsed: 0.129 s
% 1.55/0.58  % (14443)------------------------------
% 1.55/0.58  % (14443)------------------------------
% 1.55/0.58  % (14439)Refutation not found, incomplete strategy% (14439)------------------------------
% 1.55/0.58  % (14439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (14439)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (14439)Memory used [KB]: 11001
% 1.55/0.58  % (14439)Time elapsed: 0.190 s
% 1.55/0.58  % (14439)------------------------------
% 1.55/0.58  % (14439)------------------------------
% 1.55/0.58  % SZS status CounterSatisfiable for theBenchmark
% 1.55/0.58  % (14437)# SZS output start Saturation.
% 1.55/0.58  cnf(u52,axiom,
% 1.55/0.58      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.55/0.58  
% 1.55/0.58  cnf(u28,negated_conjecture,
% 1.55/0.58      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.55/0.58  
% 1.55/0.58  cnf(u24,negated_conjecture,
% 1.55/0.58      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.55/0.58  
% 1.55/0.58  cnf(u125,negated_conjecture,
% 1.55/0.58      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))).
% 1.55/0.58  
% 1.55/0.58  cnf(u126,negated_conjecture,
% 1.55/0.58      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k5_xboole_0(X1,k7_subset_1(sK1,sK1,X1))).
% 1.55/0.58  
% 1.55/0.58  cnf(u63,axiom,
% 1.55/0.58      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 1.55/0.58  
% 1.55/0.58  cnf(u62,axiom,
% 1.55/0.58      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k7_subset_1(X2,X2,X1))).
% 1.55/0.58  
% 1.55/0.58  cnf(u127,axiom,
% 1.55/0.58      ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k5_xboole_0(X2,k7_subset_1(X3,X3,X2)) = k4_subset_1(X3,X2,X3)).
% 1.55/0.58  
% 1.55/0.58  cnf(u26,negated_conjecture,
% 1.55/0.58      r1_xboole_0(sK1,sK2)).
% 1.55/0.58  
% 1.55/0.58  cnf(u48,axiom,
% 1.55/0.58      ~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))).
% 1.55/0.58  
% 1.55/0.58  cnf(u58,negated_conjecture,
% 1.55/0.58      k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,sK2))).
% 1.55/0.58  
% 1.55/0.58  cnf(u54,axiom,
% 1.55/0.58      k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))).
% 1.55/0.58  
% 1.55/0.58  cnf(u44,axiom,
% 1.55/0.58      k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))).
% 1.55/0.58  
% 1.55/0.58  cnf(u170,negated_conjecture,
% 1.55/0.58      sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 1.55/0.58  
% 1.55/0.58  cnf(u88,negated_conjecture,
% 1.55/0.58      sK2 = k7_subset_1(sK2,sK2,sK1)).
% 1.55/0.58  
% 1.55/0.58  cnf(u183,negated_conjecture,
% 1.55/0.58      sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2)).
% 1.55/0.58  
% 1.55/0.58  cnf(u77,negated_conjecture,
% 1.55/0.58      sK1 = k7_subset_1(sK1,sK1,sK2)).
% 1.55/0.58  
% 1.55/0.58  cnf(u306,negated_conjecture,
% 1.55/0.58      k7_subset_1(sK2,sK2,u1_struct_0(sK0)) = k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_struct_0(sK0))).
% 1.55/0.58  
% 1.55/0.58  cnf(u323,negated_conjecture,
% 1.55/0.58      k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))).
% 1.55/0.58  
% 1.55/0.58  cnf(u290,negated_conjecture,
% 1.55/0.58      k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)).
% 1.55/0.58  
% 1.55/0.58  cnf(u274,negated_conjecture,
% 1.55/0.58      k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),sK2)).
% 1.55/0.58  
% 1.55/0.58  cnf(u67,negated_conjecture,
% 1.55/0.58      k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0)).
% 1.55/0.58  
% 1.55/0.58  cnf(u66,negated_conjecture,
% 1.55/0.58      k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1)).
% 1.55/0.58  
% 1.55/0.58  cnf(u244,axiom,
% 1.55/0.58      k7_subset_1(X4,X4,X3) = k7_subset_1(k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),X3)).
% 1.55/0.58  
% 1.55/0.58  cnf(u154,axiom,
% 1.55/0.58      k7_subset_1(X2,X2,X3) = k7_subset_1(k5_xboole_0(X2,k7_subset_1(X3,X3,X2)),k5_xboole_0(X2,k7_subset_1(X3,X3,X2)),X3)).
% 1.55/0.58  
% 1.55/0.58  cnf(u61,axiom,
% 1.55/0.58      k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))).
% 1.55/0.58  
% 1.55/0.58  cnf(u279,negated_conjecture,
% 1.55/0.58      k1_xboole_0 = k7_subset_1(sK2,sK2,k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)))).
% 1.55/0.58  
% 1.55/0.58  cnf(u187,negated_conjecture,
% 1.55/0.58      k1_xboole_0 = k7_subset_1(sK2,sK2,k2_struct_0(sK0))).
% 1.55/0.58  
% 1.55/0.58  cnf(u295,negated_conjecture,
% 1.55/0.58      k1_xboole_0 = k7_subset_1(sK1,sK1,k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))).
% 1.55/0.58  
% 1.55/0.58  cnf(u174,negated_conjecture,
% 1.55/0.58      k1_xboole_0 = k7_subset_1(sK1,sK1,k2_struct_0(sK0))).
% 1.55/0.58  
% 1.55/0.58  cnf(u329,negated_conjecture,
% 1.55/0.58      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))).
% 1.55/0.58  
% 1.55/0.58  cnf(u312,negated_conjecture,
% 1.55/0.58      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)))).
% 1.55/0.58  
% 1.55/0.58  cnf(u491,axiom,
% 1.55/0.58      k1_xboole_0 = k7_subset_1(k5_xboole_0(X4,k7_subset_1(X3,X3,X4)),k5_xboole_0(X4,k7_subset_1(X3,X3,X4)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)))).
% 1.55/0.58  
% 1.55/0.58  cnf(u76,axiom,
% 1.55/0.58      k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1)).
% 1.55/0.58  
% 1.55/0.58  cnf(u464,axiom,
% 1.55/0.58      k1_xboole_0 = k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1)))).
% 1.55/0.58  
% 1.55/0.58  cnf(u442,axiom,
% 1.55/0.58      k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2)))).
% 1.55/0.58  
% 1.55/0.58  cnf(u198,axiom,
% 1.55/0.58      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 1.55/0.58  
% 1.55/0.58  cnf(u208,negated_conjecture,
% 1.55/0.58      sK2 = k4_subset_1(u1_struct_0(sK0),sK2,sK2)).
% 1.55/0.58  
% 1.55/0.58  cnf(u207,negated_conjecture,
% 1.55/0.58      sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.55/0.58  
% 1.55/0.58  cnf(u142,negated_conjecture,
% 1.55/0.58      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 1.55/0.58  
% 1.55/0.58  cnf(u25,negated_conjecture,
% 1.55/0.58      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 1.55/0.58  
% 1.55/0.58  cnf(u225,negated_conjecture,
% 1.55/0.58      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 1.55/0.58  
% 1.55/0.58  cnf(u221,negated_conjecture,
% 1.55/0.58      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 1.55/0.58  
% 1.55/0.58  cnf(u228,negated_conjecture,
% 1.55/0.58      k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 1.55/0.58  
% 1.55/0.58  cnf(u224,negated_conjecture,
% 1.55/0.58      k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 1.55/0.58  
% 1.55/0.58  cnf(u219,negated_conjecture,
% 1.55/0.58      k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 1.55/0.58  
% 1.55/0.58  cnf(u218,negated_conjecture,
% 1.55/0.58      k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 1.55/0.58  
% 1.55/0.58  cnf(u33,axiom,
% 1.55/0.58      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 1.55/0.58  
% 1.55/0.58  cnf(u162,negated_conjecture,
% 1.55/0.58      sK2 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))))).
% 1.55/0.58  
% 1.55/0.58  cnf(u164,negated_conjecture,
% 1.55/0.58      sK1 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))))).
% 1.55/0.58  
% 1.55/0.58  cnf(u133,negated_conjecture,
% 1.55/0.58      k2_struct_0(sK0) = k5_xboole_0(sK2,sK1)).
% 1.55/0.58  
% 1.55/0.58  cnf(u132,negated_conjecture,
% 1.55/0.58      k2_struct_0(sK0) = k5_xboole_0(sK1,sK2)).
% 1.55/0.58  
% 1.55/0.58  cnf(u222,negated_conjecture,
% 1.55/0.58      k7_subset_1(sK2,sK2,u1_struct_0(sK0)) = k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)))))).
% 1.55/0.58  
% 1.55/0.58  cnf(u226,negated_conjecture,
% 1.55/0.58      k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))))).
% 1.55/0.58  
% 1.55/0.58  cnf(u227,negated_conjecture,
% 1.55/0.58      k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))))).
% 1.55/0.58  
% 1.55/0.58  cnf(u223,negated_conjecture,
% 1.55/0.58      k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)))))).
% 1.55/0.58  
% 1.55/0.58  cnf(u147,axiom,
% 1.55/0.58      k7_subset_1(X0,X0,X1) = k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k7_subset_1(X0,X0,X1)))))).
% 1.55/0.58  
% 1.55/0.58  cnf(u68,axiom,
% 1.55/0.58      k7_subset_1(X0,X0,X1) = k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(X1,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))))).
% 1.55/0.58  
% 1.55/0.58  cnf(u70,axiom,
% 1.55/0.58      k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))).
% 1.55/0.58  
% 1.55/0.58  cnf(u771,axiom,
% 1.55/0.58      k5_xboole_0(X3,k7_subset_1(X4,X4,X3)) = k5_xboole_0(k5_xboole_0(X4,k7_subset_1(X3,X3,X4)),k1_xboole_0)).
% 1.55/0.58  
% 1.55/0.58  cnf(u69,axiom,
% 1.55/0.58      k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1))).
% 1.55/0.58  
% 1.55/0.58  cnf(u948,axiom,
% 1.55/0.58      k1_xboole_0 = k5_xboole_0(k5_xboole_0(X4,k7_subset_1(X5,X5,X4)),k1_setfam_1(k2_tarski(k5_xboole_0(X4,k7_subset_1(X5,X5,X4)),k5_xboole_0(X5,k7_subset_1(X4,X4,X5)))))).
% 1.55/0.58  
% 1.55/0.58  cnf(u490,axiom,
% 1.55/0.58      k1_xboole_0 = k5_xboole_0(k5_xboole_0(X4,k7_subset_1(X3,X3,X4)),k1_setfam_1(k2_tarski(k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X4,k7_subset_1(X3,X3,X4)))))).
% 1.55/0.58  
% 1.55/0.58  cnf(u157,axiom,
% 1.55/0.58      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0)))).
% 1.55/0.58  
% 1.55/0.58  cnf(u75,axiom,
% 1.55/0.58      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 1.55/0.58  
% 1.55/0.58  cnf(u230,axiom,
% 1.55/0.58      k4_subset_1(X0,X0,X0) = X0).
% 1.55/0.58  
% 1.55/0.58  cnf(u29,axiom,
% 1.55/0.58      k2_subset_1(X0) = X0).
% 1.55/0.58  
% 1.55/0.58  cnf(u96,axiom,
% 1.55/0.58      k5_xboole_0(k1_xboole_0,X0) = X0).
% 1.55/0.58  
% 1.55/0.58  cnf(u51,axiom,
% 1.55/0.58      k5_xboole_0(X0,k1_xboole_0) = X0).
% 1.55/0.58  
% 1.55/0.58  cnf(u27,negated_conjecture,
% 1.55/0.58      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 1.55/0.58  
% 1.55/0.58  % (14437)# SZS output end Saturation.
% 1.55/0.58  % (14437)------------------------------
% 1.55/0.58  % (14437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (14437)Termination reason: Satisfiable
% 1.55/0.58  
% 1.55/0.58  % (14437)Memory used [KB]: 6780
% 1.55/0.58  % (14437)Time elapsed: 0.177 s
% 1.55/0.58  % (14437)------------------------------
% 1.55/0.58  % (14437)------------------------------
% 1.55/0.59  % (14427)Success in time 0.224 s
%------------------------------------------------------------------------------
