%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:01 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   36 (  36 expanded)
%              Number of leaves         :   36 (  36 expanded)
%              Depth                    :    0
%              Number of atoms          :   45 (  45 expanded)
%              Number of equality atoms :   32 (  32 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u25,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u34,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u49,negated_conjecture,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK2,X2) = k2_xboole_0(sK2,X2) )).

cnf(u50,negated_conjecture,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,X3) = k2_xboole_0(sK1,X3) )).

cnf(u29,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )).

cnf(u30,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u32,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u33,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) )).

cnf(u48,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X1,X0) = k2_xboole_0(X1,X0) )).

cnf(u23,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u31,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 )).

cnf(u43,negated_conjecture,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u44,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u62,negated_conjecture,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u35,negated_conjecture,
    ( sK1 = k4_xboole_0(sK1,sK2) )).

cnf(u57,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

cnf(u22,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u47,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X3) = k4_xboole_0(sK1,X3) )).

cnf(u46,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X2) = k4_xboole_0(sK2,X2) )).

cnf(u58,axiom,
    ( k4_subset_1(X0,X0,X0) = k2_xboole_0(X0,X0) )).

cnf(u60,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u59,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(u1_struct_0(sK0),sK2) )).

cnf(u54,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u56,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) )).

cnf(u51,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k2_xboole_0(sK2,u1_struct_0(sK0)) )).

cnf(u53,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1) )).

cnf(u52,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) )).

cnf(u42,axiom,
    ( k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0 )).

cnf(u26,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u45,axiom,
    ( k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u38,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1) )).

cnf(u37,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK0),sK2) = k3_subset_1(u1_struct_0(sK0),sK2) )).

cnf(u36,axiom,
    ( k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) )).

cnf(u28,axiom,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) )).

cnf(u24,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (19821)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.45  % (19813)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.45  % (19815)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.46  % (19822)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.46  % (19813)Refutation not found, incomplete strategy% (19813)------------------------------
% 0.21/0.46  % (19813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (19813)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  % (19814)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  
% 0.21/0.46  % (19813)Memory used [KB]: 6268
% 0.21/0.46  % (19813)Time elapsed: 0.054 s
% 0.21/0.46  % (19813)------------------------------
% 0.21/0.46  % (19813)------------------------------
% 0.21/0.46  % (19814)Refutation not found, incomplete strategy% (19814)------------------------------
% 0.21/0.46  % (19814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (19814)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (19814)Memory used [KB]: 10618
% 0.21/0.46  % (19814)Time elapsed: 0.053 s
% 0.21/0.46  % (19814)------------------------------
% 0.21/0.46  % (19814)------------------------------
% 0.21/0.47  % (19822)Refutation not found, incomplete strategy% (19822)------------------------------
% 0.21/0.47  % (19822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (19822)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (19822)Memory used [KB]: 10746
% 0.21/0.47  % (19822)Time elapsed: 0.059 s
% 0.21/0.47  % (19822)------------------------------
% 0.21/0.47  % (19822)------------------------------
% 0.21/0.47  % (19829)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (19829)Refutation not found, incomplete strategy% (19829)------------------------------
% 0.21/0.47  % (19829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (19829)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (19829)Memory used [KB]: 6140
% 0.21/0.47  % (19829)Time elapsed: 0.025 s
% 0.21/0.47  % (19829)------------------------------
% 0.21/0.47  % (19829)------------------------------
% 0.21/0.47  % (19819)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (19819)Refutation not found, incomplete strategy% (19819)------------------------------
% 0.21/0.47  % (19819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (19819)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (19819)Memory used [KB]: 10746
% 0.21/0.47  % (19819)Time elapsed: 0.070 s
% 0.21/0.47  % (19819)------------------------------
% 0.21/0.47  % (19819)------------------------------
% 0.21/0.48  % (19823)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (19823)Refutation not found, incomplete strategy% (19823)------------------------------
% 0.21/0.48  % (19823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (19823)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (19823)Memory used [KB]: 6140
% 0.21/0.48  % (19823)Time elapsed: 0.063 s
% 0.21/0.48  % (19823)------------------------------
% 0.21/0.48  % (19823)------------------------------
% 0.21/0.48  % (19827)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (19817)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (19832)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (19817)Refutation not found, incomplete strategy% (19817)------------------------------
% 0.21/0.48  % (19817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (19817)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (19817)Memory used [KB]: 1663
% 0.21/0.48  % (19817)Time elapsed: 0.073 s
% 0.21/0.48  % (19817)------------------------------
% 0.21/0.48  % (19817)------------------------------
% 0.21/0.48  % (19826)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (19834)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (19826)Refutation not found, incomplete strategy% (19826)------------------------------
% 0.21/0.48  % (19826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (19826)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (19826)Memory used [KB]: 1663
% 0.21/0.48  % (19826)Time elapsed: 0.081 s
% 0.21/0.48  % (19826)------------------------------
% 0.21/0.48  % (19826)------------------------------
% 0.21/0.48  % (19834)Refutation not found, incomplete strategy% (19834)------------------------------
% 0.21/0.48  % (19834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (19834)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (19834)Memory used [KB]: 10490
% 0.21/0.48  % (19834)Time elapsed: 0.077 s
% 0.21/0.48  % (19834)------------------------------
% 0.21/0.48  % (19834)------------------------------
% 0.21/0.48  % (19816)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (19818)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (19820)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (19831)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (19816)Refutation not found, incomplete strategy% (19816)------------------------------
% 0.21/0.49  % (19816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19816)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (19816)Memory used [KB]: 10746
% 0.21/0.49  % (19816)Time elapsed: 0.075 s
% 0.21/0.49  % (19816)------------------------------
% 0.21/0.49  % (19816)------------------------------
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (19831)# SZS output start Saturation.
% 0.21/0.49  cnf(u25,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.49  
% 0.21/0.49  cnf(u21,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.49  
% 0.21/0.49  cnf(u34,axiom,
% 0.21/0.49      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u49,negated_conjecture,
% 0.21/0.49      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK2,X2) = k2_xboole_0(sK2,X2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u50,negated_conjecture,
% 0.21/0.49      ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X3) = k2_xboole_0(sK1,X3)).
% 0.21/0.49  
% 0.21/0.49  cnf(u29,axiom,
% 0.21/0.49      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u30,axiom,
% 0.21/0.49      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.21/0.49  
% 0.21/0.49  cnf(u32,axiom,
% 0.21/0.49      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u33,axiom,
% 0.21/0.49      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u48,axiom,
% 0.21/0.49      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k4_subset_1(X1,X1,X0) = k2_xboole_0(X1,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u23,negated_conjecture,
% 0.21/0.49      r1_xboole_0(sK1,sK2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u31,axiom,
% 0.21/0.49      ~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0).
% 0.21/0.49  
% 0.21/0.49  cnf(u43,negated_conjecture,
% 0.21/0.49      sK2 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.21/0.49  
% 0.21/0.49  cnf(u44,negated_conjecture,
% 0.21/0.49      sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.21/0.49  
% 0.21/0.49  cnf(u62,negated_conjecture,
% 0.21/0.49      sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u35,negated_conjecture,
% 0.21/0.49      sK1 = k4_xboole_0(sK1,sK2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u57,negated_conjecture,
% 0.21/0.49      k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u22,negated_conjecture,
% 0.21/0.49      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u47,negated_conjecture,
% 0.21/0.49      k7_subset_1(u1_struct_0(sK0),sK1,X3) = k4_xboole_0(sK1,X3)).
% 0.21/0.49  
% 0.21/0.49  cnf(u46,negated_conjecture,
% 0.21/0.49      k7_subset_1(u1_struct_0(sK0),sK2,X2) = k4_xboole_0(sK2,X2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u58,axiom,
% 0.21/0.49      k4_subset_1(X0,X0,X0) = k2_xboole_0(X0,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u60,negated_conjecture,
% 0.21/0.49      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),sK1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u59,negated_conjecture,
% 0.21/0.49      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(u1_struct_0(sK0),sK2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u54,negated_conjecture,
% 0.21/0.49      k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u56,negated_conjecture,
% 0.21/0.49      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u51,negated_conjecture,
% 0.21/0.49      k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k2_xboole_0(sK2,u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u53,negated_conjecture,
% 0.21/0.49      k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u52,negated_conjecture,
% 0.21/0.49      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u42,axiom,
% 0.21/0.49      k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0).
% 0.21/0.49  
% 0.21/0.49  cnf(u26,axiom,
% 0.21/0.49      k2_subset_1(X0) = X0).
% 0.21/0.49  
% 0.21/0.49  cnf(u45,axiom,
% 0.21/0.49      k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u38,negated_conjecture,
% 0.21/0.49      k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u37,negated_conjecture,
% 0.21/0.49      k4_xboole_0(u1_struct_0(sK0),sK2) = k3_subset_1(u1_struct_0(sK0),sK2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u36,axiom,
% 0.21/0.49      k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u28,axiom,
% 0.21/0.49      k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u24,negated_conjecture,
% 0.21/0.49      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.21/0.49  
% 0.21/0.49  % (19831)# SZS output end Saturation.
% 0.21/0.49  % (19831)------------------------------
% 0.21/0.49  % (19831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19831)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (19831)Memory used [KB]: 1663
% 0.21/0.49  % (19831)Time elapsed: 0.079 s
% 0.21/0.49  % (19831)------------------------------
% 0.21/0.49  % (19831)------------------------------
% 0.21/0.49  % (19810)Success in time 0.134 s
%------------------------------------------------------------------------------
