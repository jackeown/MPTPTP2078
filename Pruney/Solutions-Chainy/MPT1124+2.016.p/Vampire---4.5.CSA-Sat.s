%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:23 EST 2020

% Result     : CounterSatisfiable 1.73s
% Output     : Saturation 1.73s
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
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:48:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (7669)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (7669)Refutation not found, incomplete strategy% (7669)------------------------------
% 0.21/0.49  % (7669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7669)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7669)Memory used [KB]: 10618
% 0.21/0.49  % (7669)Time elapsed: 0.069 s
% 0.21/0.49  % (7669)------------------------------
% 0.21/0.49  % (7669)------------------------------
% 0.21/0.50  % (7677)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (7665)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (7677)Refutation not found, incomplete strategy% (7677)------------------------------
% 0.21/0.51  % (7677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7677)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (7677)Memory used [KB]: 10618
% 0.21/0.51  % (7677)Time elapsed: 0.080 s
% 0.21/0.51  % (7677)------------------------------
% 0.21/0.51  % (7677)------------------------------
% 0.21/0.51  % (7673)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (7673)Refutation not found, incomplete strategy% (7673)------------------------------
% 0.21/0.52  % (7673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7673)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7673)Memory used [KB]: 6012
% 0.21/0.52  % (7673)Time elapsed: 0.083 s
% 0.21/0.52  % (7673)------------------------------
% 0.21/0.52  % (7673)------------------------------
% 0.21/0.52  % (7667)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (7665)Refutation not found, incomplete strategy% (7665)------------------------------
% 0.21/0.52  % (7665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7665)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7665)Memory used [KB]: 10618
% 0.21/0.52  % (7665)Time elapsed: 0.081 s
% 0.21/0.52  % (7665)------------------------------
% 0.21/0.52  % (7665)------------------------------
% 0.21/0.53  % (7679)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.53  % (7678)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.53  % (7668)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (7672)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.53  % (7674)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.53  % (7672)Refutation not found, incomplete strategy% (7672)------------------------------
% 0.21/0.53  % (7672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (7672)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (7672)Memory used [KB]: 10618
% 0.21/0.53  % (7672)Time elapsed: 0.064 s
% 0.21/0.53  % (7672)------------------------------
% 0.21/0.53  % (7672)------------------------------
% 0.21/0.53  % (7674)Refutation not found, incomplete strategy% (7674)------------------------------
% 0.21/0.53  % (7674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (7674)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (7674)Memory used [KB]: 10618
% 0.21/0.53  % (7674)Time elapsed: 0.101 s
% 0.21/0.53  % (7674)------------------------------
% 0.21/0.53  % (7674)------------------------------
% 0.21/0.54  % (7678)Refutation not found, incomplete strategy% (7678)------------------------------
% 0.21/0.54  % (7678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7678)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7678)Memory used [KB]: 6140
% 0.21/0.54  % (7678)Time elapsed: 0.066 s
% 0.21/0.54  % (7678)------------------------------
% 0.21/0.54  % (7678)------------------------------
% 0.21/0.54  % (7663)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (7663)Refutation not found, incomplete strategy% (7663)------------------------------
% 0.21/0.54  % (7663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7663)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7663)Memory used [KB]: 6140
% 0.21/0.54  % (7663)Time elapsed: 0.105 s
% 0.21/0.54  % (7663)------------------------------
% 0.21/0.54  % (7663)------------------------------
% 0.21/0.54  % (7679)Refutation not found, incomplete strategy% (7679)------------------------------
% 0.21/0.54  % (7679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7679)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7679)Memory used [KB]: 10746
% 0.21/0.54  % (7679)Time elapsed: 0.099 s
% 0.21/0.54  % (7679)------------------------------
% 0.21/0.54  % (7679)------------------------------
% 0.21/0.54  % (7676)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.54  % (7681)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.54  % (7676)Refutation not found, incomplete strategy% (7676)------------------------------
% 0.21/0.54  % (7676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7676)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7676)Memory used [KB]: 1663
% 0.21/0.54  % (7676)Time elapsed: 0.120 s
% 0.21/0.54  % (7676)------------------------------
% 0.21/0.54  % (7676)------------------------------
% 0.21/0.55  % (7681)Refutation not found, incomplete strategy% (7681)------------------------------
% 0.21/0.55  % (7681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7681)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7681)Memory used [KB]: 1663
% 0.21/0.55  % (7681)Time elapsed: 0.115 s
% 0.21/0.55  % (7681)------------------------------
% 0.21/0.55  % (7681)------------------------------
% 1.53/0.55  % (7664)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.53/0.55  % (7666)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.53/0.55  % (7664)Refutation not found, incomplete strategy% (7664)------------------------------
% 1.53/0.55  % (7664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.55  % (7670)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.53/0.55  % (7664)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.55  
% 1.53/0.55  % (7664)Memory used [KB]: 10618
% 1.53/0.55  % (7664)Time elapsed: 0.112 s
% 1.53/0.55  % (7664)------------------------------
% 1.53/0.55  % (7664)------------------------------
% 1.53/0.55  % (7671)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.53/0.55  % (7666)Refutation not found, incomplete strategy% (7666)------------------------------
% 1.53/0.55  % (7666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.55  % (7666)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.55  
% 1.53/0.55  % (7666)Memory used [KB]: 10618
% 1.53/0.55  % (7666)Time elapsed: 0.129 s
% 1.53/0.55  % (7666)------------------------------
% 1.53/0.55  % (7666)------------------------------
% 1.53/0.55  % (7682)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.53/0.56  % (7675)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.53/0.56  % (7683)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.53/0.56  % (7683)Refutation not found, incomplete strategy% (7683)------------------------------
% 1.53/0.56  % (7683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (7683)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (7683)Memory used [KB]: 10618
% 1.53/0.56  % (7683)Time elapsed: 0.136 s
% 1.53/0.56  % (7683)------------------------------
% 1.53/0.56  % (7683)------------------------------
% 1.53/0.56  % (7680)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.73/0.57  % SZS status CounterSatisfiable for theBenchmark
% 1.73/0.57  % (7680)# SZS output start Saturation.
% 1.73/0.57  cnf(u19,negated_conjecture,
% 1.73/0.57      m1_pre_topc(sK1,sK0)).
% 1.73/0.57  
% 1.73/0.57  cnf(u31,axiom,
% 1.73/0.57      ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)).
% 1.73/0.57  
% 1.73/0.57  cnf(u30,axiom,
% 1.73/0.57      ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X0)).
% 1.73/0.57  
% 1.73/0.57  cnf(u37,negated_conjecture,
% 1.73/0.57      l1_pre_topc(sK1)).
% 1.73/0.57  
% 1.73/0.57  cnf(u20,negated_conjecture,
% 1.73/0.57      l1_pre_topc(sK0)).
% 1.73/0.57  
% 1.73/0.57  cnf(u40,negated_conjecture,
% 1.73/0.57      r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))).
% 1.73/0.57  
% 1.73/0.57  cnf(u29,axiom,
% 1.73/0.57      ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | m1_pre_topc(X1,X0)).
% 1.73/0.57  
% 1.73/0.57  cnf(u23,axiom,
% 1.73/0.57      ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | r2_hidden(sK5(X0,X1),u1_pre_topc(X0)) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0)).
% 1.73/0.57  
% 1.73/0.57  cnf(u22,axiom,
% 1.73/0.57      ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0)).
% 1.73/0.57  
% 1.73/0.57  cnf(u24,axiom,
% 1.73/0.57      ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | sK3(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1)) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0)).
% 1.73/0.57  
% 1.73/0.57  cnf(u32,axiom,
% 1.73/0.57      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 1.73/0.57  
% 1.73/0.57  cnf(u34,axiom,
% 1.73/0.57      ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)).
% 1.73/0.57  
% 1.73/0.57  cnf(u45,negated_conjecture,
% 1.73/0.57      m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK0)))).
% 1.73/0.57  
% 1.73/0.57  cnf(u17,negated_conjecture,
% 1.73/0.57      m1_subset_1(sK2,u1_struct_0(sK1))).
% 1.73/0.57  
% 1.73/0.57  cnf(u35,axiom,
% 1.73/0.57      ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X3,u1_pre_topc(X0)) | r2_hidden(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0)).
% 1.73/0.57  
% 1.73/0.57  cnf(u26,axiom,
% 1.73/0.57      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | r2_hidden(sK4(X0,X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0)).
% 1.73/0.57  
% 1.73/0.57  cnf(u25,axiom,
% 1.73/0.57      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0)).
% 1.73/0.57  
% 1.73/0.57  cnf(u27,axiom,
% 1.73/0.57      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2 | ~r2_hidden(X2,u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0)).
% 1.73/0.57  
% 1.73/0.57  cnf(u21,axiom,
% 1.73/0.57      ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~r2_hidden(X3,u1_pre_topc(X0)) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK3(X0,X1) | ~r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X0)).
% 1.73/0.57  
% 1.73/0.57  cnf(u33,axiom,
% 1.73/0.57      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 1.73/0.57  
% 1.73/0.57  cnf(u18,negated_conjecture,
% 1.73/0.57      ~m1_subset_1(sK2,u1_struct_0(sK0))).
% 1.73/0.57  
% 1.73/0.57  % (7680)# SZS output end Saturation.
% 1.73/0.57  % (7680)------------------------------
% 1.73/0.57  % (7680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.57  % (7680)Termination reason: Satisfiable
% 1.73/0.57  
% 1.73/0.57  % (7680)Memory used [KB]: 1663
% 1.73/0.57  % (7680)Time elapsed: 0.136 s
% 1.73/0.57  % (7680)------------------------------
% 1.73/0.57  % (7680)------------------------------
% 1.73/0.57  % (7662)Success in time 0.205 s
%------------------------------------------------------------------------------
