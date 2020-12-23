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
% DateTime   : Thu Dec  3 13:09:23 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   21 (  21 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    0
%              Number of atoms          :   77 (  77 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u19,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) )).

cnf(u31,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(X1) )).

cnf(u30,axiom,
    ( ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X1)
    | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
    | ~ l1_pre_topc(X0) )).

cnf(u37,negated_conjecture,
    ( l1_pre_topc(sK1) )).

cnf(u20,negated_conjecture,
    ( l1_pre_topc(sK0) )).

cnf(u40,negated_conjecture,
    ( r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0)) )).

cnf(u29,axiom,
    ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(X1,X0) )).

cnf(u23,axiom,
    ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | r2_hidden(sK5(X0,X1),u1_pre_topc(X0))
    | r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
    | m1_pre_topc(X1,X0) )).

cnf(u22,axiom,
    ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
    | m1_pre_topc(X1,X0) )).

cnf(u24,axiom,
    ( ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | sK3(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))
    | r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
    | m1_pre_topc(X1,X0) )).

cnf(u32,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u34,axiom,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2) )).

cnf(u45,negated_conjecture,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK0))) )).

cnf(u17,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) )).

cnf(u35,axiom,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X3,u1_pre_topc(X0))
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,X0) )).

cnf(u26,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | r2_hidden(sK4(X0,X1,X2),u1_pre_topc(X0))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,X0) )).

cnf(u25,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,X0) )).

cnf(u27,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,X0) )).

cnf(u21,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ r2_hidden(X3,u1_pre_topc(X0))
    | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK3(X0,X1)
    | ~ r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
    | m1_pre_topc(X1,X0) )).

cnf(u33,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u18,negated_conjecture,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:16:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.41  % (1408)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.42  % (1408)Refutation not found, incomplete strategy% (1408)------------------------------
% 0.20/0.42  % (1408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (1408)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.42  
% 0.20/0.42  % (1408)Memory used [KB]: 1663
% 0.20/0.42  % (1408)Time elapsed: 0.004 s
% 0.20/0.42  % (1408)------------------------------
% 0.20/0.42  % (1408)------------------------------
% 0.20/0.46  % (1402)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (1400)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (1409)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (1411)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  % (1403)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (1396)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (1396)Refutation not found, incomplete strategy% (1396)------------------------------
% 0.20/0.49  % (1396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1396)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1396)Memory used [KB]: 10618
% 0.20/0.49  % (1396)Time elapsed: 0.069 s
% 0.20/0.49  % (1396)------------------------------
% 0.20/0.49  % (1396)------------------------------
% 0.20/0.49  % (1398)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (1397)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (1398)Refutation not found, incomplete strategy% (1398)------------------------------
% 0.20/0.49  % (1398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1398)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1398)Memory used [KB]: 10618
% 0.20/0.49  % (1398)Time elapsed: 0.074 s
% 0.20/0.49  % (1398)------------------------------
% 0.20/0.49  % (1398)------------------------------
% 0.20/0.49  % (1411)Refutation not found, incomplete strategy% (1411)------------------------------
% 0.20/0.49  % (1411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1411)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1411)Memory used [KB]: 10746
% 0.20/0.49  % (1411)Time elapsed: 0.074 s
% 0.20/0.49  % (1411)------------------------------
% 0.20/0.49  % (1411)------------------------------
% 0.20/0.49  % (1407)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (1415)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (1415)Refutation not found, incomplete strategy% (1415)------------------------------
% 0.20/0.50  % (1415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1415)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (1415)Memory used [KB]: 10618
% 0.20/0.50  % (1415)Time elapsed: 0.084 s
% 0.20/0.50  % (1415)------------------------------
% 0.20/0.50  % (1415)------------------------------
% 0.20/0.50  % (1409)Refutation not found, incomplete strategy% (1409)------------------------------
% 0.20/0.50  % (1409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1409)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (1409)Memory used [KB]: 10618
% 0.20/0.50  % (1409)Time elapsed: 0.048 s
% 0.20/0.50  % (1409)------------------------------
% 0.20/0.50  % (1409)------------------------------
% 0.20/0.50  % (1410)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (1397)Refutation not found, incomplete strategy% (1397)------------------------------
% 0.20/0.50  % (1397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1397)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (1397)Memory used [KB]: 10618
% 0.20/0.50  % (1397)Time elapsed: 0.083 s
% 0.20/0.50  % (1397)------------------------------
% 0.20/0.50  % (1397)------------------------------
% 0.20/0.50  % (1413)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (1406)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (1413)Refutation not found, incomplete strategy% (1413)------------------------------
% 0.20/0.50  % (1413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1413)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (1413)Memory used [KB]: 1663
% 0.20/0.50  % (1413)Time elapsed: 0.098 s
% 0.20/0.50  % (1413)------------------------------
% 0.20/0.50  % (1413)------------------------------
% 0.20/0.50  % (1405)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (1405)Refutation not found, incomplete strategy% (1405)------------------------------
% 0.20/0.51  % (1405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (1405)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (1405)Memory used [KB]: 6012
% 0.20/0.51  % (1405)Time elapsed: 0.097 s
% 0.20/0.51  % (1399)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  % (1405)------------------------------
% 0.20/0.51  % (1405)------------------------------
% 0.20/0.51  % (1406)Refutation not found, incomplete strategy% (1406)------------------------------
% 0.20/0.51  % (1406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (1406)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (1406)Memory used [KB]: 10618
% 0.20/0.51  % (1406)Time elapsed: 0.098 s
% 0.20/0.51  % (1406)------------------------------
% 0.20/0.51  % (1406)------------------------------
% 0.20/0.51  % (1414)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (1395)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (1395)Refutation not found, incomplete strategy% (1395)------------------------------
% 0.20/0.51  % (1395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (1395)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (1395)Memory used [KB]: 6140
% 0.20/0.51  % (1395)Time elapsed: 0.091 s
% 0.20/0.51  % (1395)------------------------------
% 0.20/0.51  % (1395)------------------------------
% 0.20/0.51  % (1410)Refutation not found, incomplete strategy% (1410)------------------------------
% 0.20/0.51  % (1410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (1410)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (1410)Memory used [KB]: 6140
% 0.20/0.51  % (1410)Time elapsed: 0.098 s
% 0.20/0.51  % (1410)------------------------------
% 0.20/0.51  % (1410)------------------------------
% 0.20/0.51  % (1412)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.51  % (1412)# SZS output start Saturation.
% 0.20/0.51  cnf(u19,negated_conjecture,
% 0.20/0.51      m1_pre_topc(sK1,sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u31,axiom,
% 0.20/0.51      ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u30,axiom,
% 0.20/0.51      ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u37,negated_conjecture,
% 0.20/0.51      l1_pre_topc(sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u20,negated_conjecture,
% 0.20/0.51      l1_pre_topc(sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u40,negated_conjecture,
% 0.20/0.51      r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u29,axiom,
% 0.20/0.51      ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | m1_pre_topc(X1,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u23,axiom,
% 0.20/0.51      ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | r2_hidden(sK5(X0,X1),u1_pre_topc(X0)) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u22,axiom,
% 0.20/0.51      ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u24,axiom,
% 0.20/0.51      ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | sK3(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1)) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u32,axiom,
% 0.20/0.51      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u34,axiom,
% 0.20/0.51      ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u45,negated_conjecture,
% 0.20/0.51      m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u17,negated_conjecture,
% 0.20/0.51      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u35,axiom,
% 0.20/0.51      ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X3,u1_pre_topc(X0)) | r2_hidden(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u26,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | r2_hidden(sK4(X0,X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u25,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u27,axiom,
% 0.20/0.51      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2 | ~r2_hidden(X2,u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u21,axiom,
% 0.20/0.51      ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~r2_hidden(X3,u1_pre_topc(X0)) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK3(X0,X1) | ~r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u33,axiom,
% 0.20/0.51      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u18,negated_conjecture,
% 0.20/0.51      ~m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  % (1412)# SZS output end Saturation.
% 0.20/0.51  % (1412)------------------------------
% 0.20/0.51  % (1412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (1412)Termination reason: Satisfiable
% 0.20/0.51  
% 0.20/0.51  % (1412)Memory used [KB]: 1663
% 0.20/0.51  % (1412)Time elapsed: 0.097 s
% 0.20/0.51  % (1412)------------------------------
% 0.20/0.51  % (1412)------------------------------
% 0.20/0.51  % (1394)Success in time 0.155 s
%------------------------------------------------------------------------------
