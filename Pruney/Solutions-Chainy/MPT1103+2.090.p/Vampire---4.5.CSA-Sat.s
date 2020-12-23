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
% DateTime   : Thu Dec  3 13:08:46 EST 2020

% Result     : CounterSatisfiable 1.59s
% Output     : Saturation 1.59s
% Verified   : 
% Statistics : Number of clauses        :   23 (  23 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    0
%              Number of atoms          :   33 (  33 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u43,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u25,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u52,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u44,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u45,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u33,axiom,
    ( ~ r1_tarski(X0,X1)
    | X0 = X1
    | r2_xboole_0(X0,X1) )).

cnf(u47,negated_conjecture,
    ( r2_xboole_0(sK1,u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) )).

cnf(u66,axiom,
    ( ~ r2_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) )).

cnf(u63,axiom,
    ( ~ r2_xboole_0(X0,X0) )).

cnf(u48,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) )).

cnf(u38,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) )).

cnf(u51,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

% (24859)Refutation not found, incomplete strategy% (24859)------------------------------
% (24859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24859)Termination reason: Refutation not found, incomplete strategy

% (24859)Memory used [KB]: 6268
% (24859)Time elapsed: 0.154 s
% (24859)------------------------------
% (24859)------------------------------
cnf(u54,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u57,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) )).

cnf(u58,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,X2,X2) )).

cnf(u23,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u39,axiom,
    ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 )).

cnf(u26,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u61,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) )).

cnf(u53,axiom,
    ( k1_xboole_0 != k7_subset_1(X1,X1,X0)
    | ~ r2_xboole_0(X0,X1) )).

cnf(u49,negated_conjecture,
    ( k1_xboole_0 != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)))
    | sK1 = u1_struct_0(sK0) )).

cnf(u42,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:10:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (24869)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (24869)Refutation not found, incomplete strategy% (24869)------------------------------
% 0.21/0.52  % (24869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24869)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24869)Memory used [KB]: 6140
% 0.21/0.52  % (24869)Time elapsed: 0.106 s
% 0.21/0.52  % (24869)------------------------------
% 0.21/0.52  % (24869)------------------------------
% 0.21/0.53  % (24861)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (24877)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (24877)Refutation not found, incomplete strategy% (24877)------------------------------
% 0.21/0.54  % (24877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24877)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24877)Memory used [KB]: 1663
% 0.21/0.54  % (24877)Time elapsed: 0.130 s
% 0.21/0.54  % (24877)------------------------------
% 0.21/0.54  % (24877)------------------------------
% 0.21/0.54  % (24855)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.46/0.55  % (24861)Refutation not found, incomplete strategy% (24861)------------------------------
% 1.46/0.55  % (24861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (24861)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (24861)Memory used [KB]: 6140
% 1.46/0.55  % (24861)Time elapsed: 0.112 s
% 1.46/0.55  % (24861)------------------------------
% 1.46/0.55  % (24861)------------------------------
% 1.46/0.55  % (24860)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.46/0.56  % (24854)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.46/0.56  % (24876)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.46/0.56  % (24856)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.46/0.56  % (24858)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.46/0.56  % (24868)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.46/0.56  % (24854)Refutation not found, incomplete strategy% (24854)------------------------------
% 1.46/0.56  % (24854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (24854)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (24854)Memory used [KB]: 1663
% 1.46/0.56  % (24854)Time elapsed: 0.134 s
% 1.46/0.56  % (24854)------------------------------
% 1.46/0.56  % (24854)------------------------------
% 1.46/0.56  % (24858)Refutation not found, incomplete strategy% (24858)------------------------------
% 1.46/0.56  % (24858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (24880)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.59/0.57  % (24882)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.59/0.57  % (24859)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.59/0.57  % (24876)Refutation not found, incomplete strategy% (24876)------------------------------
% 1.59/0.57  % (24876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (24872)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.59/0.57  % (24874)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.59/0.57  % (24858)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (24858)Memory used [KB]: 6140
% 1.59/0.57  % (24858)Time elapsed: 0.137 s
% 1.59/0.57  % (24858)------------------------------
% 1.59/0.57  % (24858)------------------------------
% 1.59/0.57  % (24864)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.59/0.57  % (24883)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.59/0.58  % (24866)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.58  % (24856)Refutation not found, incomplete strategy% (24856)------------------------------
% 1.59/0.58  % (24856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (24866)Refutation not found, incomplete strategy% (24866)------------------------------
% 1.59/0.58  % (24866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (24866)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (24866)Memory used [KB]: 6268
% 1.59/0.58  % (24866)Time elapsed: 0.164 s
% 1.59/0.58  % (24866)------------------------------
% 1.59/0.58  % (24866)------------------------------
% 1.59/0.58  % (24880)Refutation not found, incomplete strategy% (24880)------------------------------
% 1.59/0.58  % (24880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (24856)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (24856)Memory used [KB]: 10746
% 1.59/0.58  % (24856)Time elapsed: 0.155 s
% 1.59/0.58  % (24856)------------------------------
% 1.59/0.58  % (24856)------------------------------
% 1.59/0.58  % (24875)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.59/0.58  % SZS status CounterSatisfiable for theBenchmark
% 1.59/0.58  % (24876)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (24876)Memory used [KB]: 10746
% 1.59/0.58  % (24876)Time elapsed: 0.079 s
% 1.59/0.58  % (24876)------------------------------
% 1.59/0.58  % (24876)------------------------------
% 1.59/0.58  % (24860)# SZS output start Saturation.
% 1.59/0.58  cnf(u43,axiom,
% 1.59/0.58      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.59/0.58  
% 1.59/0.58  cnf(u25,negated_conjecture,
% 1.59/0.58      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.59/0.58  
% 1.59/0.58  cnf(u34,axiom,
% 1.59/0.58      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 1.59/0.58  
% 1.59/0.58  cnf(u52,axiom,
% 1.59/0.58      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 1.59/0.58  
% 1.59/0.58  cnf(u44,negated_conjecture,
% 1.59/0.58      r1_tarski(sK1,u1_struct_0(sK0))).
% 1.59/0.58  
% 1.59/0.58  cnf(u45,axiom,
% 1.59/0.58      r1_tarski(X0,X0)).
% 1.59/0.58  
% 1.59/0.58  cnf(u33,axiom,
% 1.59/0.58      ~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)).
% 1.59/0.58  
% 1.59/0.58  cnf(u47,negated_conjecture,
% 1.59/0.58      r2_xboole_0(sK1,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)).
% 1.59/0.58  
% 1.59/0.58  cnf(u66,axiom,
% 1.59/0.58      ~r2_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)).
% 1.59/0.58  
% 1.59/0.58  cnf(u63,axiom,
% 1.59/0.58      ~r2_xboole_0(X0,X0)).
% 1.59/0.58  
% 1.59/0.58  cnf(u48,axiom,
% 1.59/0.58      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0)))).
% 1.59/0.58  
% 1.59/0.58  cnf(u38,axiom,
% 1.59/0.58      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))))).
% 1.59/0.58  
% 1.59/0.58  cnf(u51,axiom,
% 1.59/0.58      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 1.59/0.58  
% 1.59/0.58  % (24859)Refutation not found, incomplete strategy% (24859)------------------------------
% 1.59/0.58  % (24859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (24859)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (24859)Memory used [KB]: 6268
% 1.59/0.58  % (24859)Time elapsed: 0.154 s
% 1.59/0.58  % (24859)------------------------------
% 1.59/0.58  % (24859)------------------------------
% 1.59/0.58  cnf(u54,negated_conjecture,
% 1.59/0.58      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 1.59/0.58  
% 1.59/0.58  cnf(u57,axiom,
% 1.59/0.58      k1_xboole_0 = k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1)))).
% 1.59/0.58  
% 1.59/0.58  cnf(u58,axiom,
% 1.59/0.58      k1_xboole_0 = k7_subset_1(X2,X2,X2)).
% 1.59/0.58  
% 1.59/0.58  cnf(u23,negated_conjecture,
% 1.59/0.58      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 1.59/0.58  
% 1.59/0.58  cnf(u39,axiom,
% 1.59/0.58      k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0).
% 1.59/0.58  
% 1.59/0.58  cnf(u26,axiom,
% 1.59/0.58      k2_subset_1(X0) = X0).
% 1.59/0.58  
% 1.59/0.58  cnf(u61,negated_conjecture,
% 1.59/0.58      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) | sK1 = u1_struct_0(sK0)).
% 1.59/0.58  
% 1.59/0.58  cnf(u53,axiom,
% 1.59/0.58      k1_xboole_0 != k7_subset_1(X1,X1,X0) | ~r2_xboole_0(X0,X1)).
% 1.59/0.58  
% 1.59/0.58  cnf(u49,negated_conjecture,
% 1.59/0.58      k1_xboole_0 != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))) | sK1 = u1_struct_0(sK0)).
% 1.59/0.58  
% 1.59/0.58  cnf(u42,negated_conjecture,
% 1.59/0.58      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.59/0.58  
% 1.59/0.58  % (24860)# SZS output end Saturation.
% 1.59/0.58  % (24860)------------------------------
% 1.59/0.58  % (24860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (24860)Termination reason: Satisfiable
% 1.59/0.58  
% 1.59/0.58  % (24860)Memory used [KB]: 6268
% 1.59/0.58  % (24860)Time elapsed: 0.097 s
% 1.59/0.58  % (24860)------------------------------
% 1.59/0.58  % (24860)------------------------------
% 1.59/0.58  % (24874)Refutation not found, incomplete strategy% (24874)------------------------------
% 1.59/0.58  % (24874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (24874)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (24874)Memory used [KB]: 10746
% 1.59/0.58  % (24874)Time elapsed: 0.159 s
% 1.59/0.58  % (24874)------------------------------
% 1.59/0.58  % (24874)------------------------------
% 1.59/0.58  % (24875)Refutation not found, incomplete strategy% (24875)------------------------------
% 1.59/0.58  % (24875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (24875)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (24875)Memory used [KB]: 1663
% 1.59/0.58  % (24875)Time elapsed: 0.160 s
% 1.59/0.58  % (24875)------------------------------
% 1.59/0.58  % (24875)------------------------------
% 1.59/0.59  % (24880)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.59  
% 1.59/0.59  % (24880)Memory used [KB]: 10746
% 1.59/0.59  % (24880)Time elapsed: 0.161 s
% 1.59/0.59  % (24880)------------------------------
% 1.59/0.59  % (24880)------------------------------
% 1.59/0.59  % (24870)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.59/0.59  % (24853)Success in time 0.221 s
%------------------------------------------------------------------------------
