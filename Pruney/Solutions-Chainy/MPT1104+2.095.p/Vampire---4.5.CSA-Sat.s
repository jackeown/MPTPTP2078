%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:02 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   34 (  34 expanded)
%              Number of leaves         :   34 (  34 expanded)
%              Depth                    :    0
%              Number of atoms          :   44 (  44 expanded)
%              Number of equality atoms :   29 (  29 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u23,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u39,axiom,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u18,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u31,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u37,negated_conjecture,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK2,X2) = k2_xboole_0(sK2,X2) )).

cnf(u38,negated_conjecture,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,X3) = k2_xboole_0(sK1,X3) )).

cnf(u26,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0)
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u29,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u30,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) )).

cnf(u36,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X1,X0) = k2_xboole_0(X1,X0) )).

cnf(u20,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u28,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 )).

cnf(u42,negated_conjecture,
    ( sK2 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK2)) )).

cnf(u43,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u56,negated_conjecture,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u32,negated_conjecture,
    ( sK1 = k4_xboole_0(sK1,sK2) )).

cnf(u50,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

cnf(u19,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u54,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u35,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X3) = k4_xboole_0(sK1,X3) )).

cnf(u34,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X2) = k4_xboole_0(sK2,X2) )).

cnf(u51,axiom,
    ( k4_subset_1(X0,X0,X0) = k2_xboole_0(X0,X0) )).

cnf(u53,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u52,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(u1_struct_0(sK0),sK2) )).

cnf(u47,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u49,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) )).

cnf(u44,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k2_xboole_0(sK2,u1_struct_0(sK0)) )).

cnf(u46,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1) )).

cnf(u45,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) )).

cnf(u24,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u33,axiom,
    ( k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u27,axiom,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) )).

cnf(u21,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:31:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.46  % (12731)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.46  % (12736)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.46  % (12732)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (12724)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.46  % (12724)Refutation not found, incomplete strategy% (12724)------------------------------
% 0.21/0.46  % (12724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (12724)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (12724)Memory used [KB]: 1663
% 0.21/0.46  % (12724)Time elapsed: 0.053 s
% 0.21/0.46  % (12724)------------------------------
% 0.21/0.46  % (12724)------------------------------
% 0.21/0.46  % (12732)Refutation not found, incomplete strategy% (12732)------------------------------
% 0.21/0.46  % (12732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (12732)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (12732)Memory used [KB]: 6012
% 0.21/0.46  % (12732)Time elapsed: 0.002 s
% 0.21/0.46  % (12732)------------------------------
% 0.21/0.46  % (12732)------------------------------
% 0.21/0.47  % (12726)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (12726)Refutation not found, incomplete strategy% (12726)------------------------------
% 0.21/0.47  % (12726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (12731)Refutation not found, incomplete strategy% (12731)------------------------------
% 0.21/0.47  % (12731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (12731)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (12731)Memory used [KB]: 10618
% 0.21/0.47  % (12731)Time elapsed: 0.066 s
% 0.21/0.47  % (12731)------------------------------
% 0.21/0.47  % (12731)------------------------------
% 0.21/0.47  % (12727)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (12734)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (12738)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (12721)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (12721)Refutation not found, incomplete strategy% (12721)------------------------------
% 0.21/0.48  % (12721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (12721)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (12721)Memory used [KB]: 10618
% 0.21/0.48  % (12721)Time elapsed: 0.075 s
% 0.21/0.48  % (12721)------------------------------
% 0.21/0.48  % (12721)------------------------------
% 0.21/0.48  % (12726)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (12726)Memory used [KB]: 10618
% 0.21/0.48  % (12726)Time elapsed: 0.030 s
% 0.21/0.48  % (12726)------------------------------
% 0.21/0.48  % (12726)------------------------------
% 0.21/0.49  % (12735)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (12733)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (12735)Refutation not found, incomplete strategy% (12735)------------------------------
% 0.21/0.49  % (12735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (12735)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (12735)Memory used [KB]: 6140
% 0.21/0.49  % (12735)Time elapsed: 0.088 s
% 0.21/0.49  % (12735)------------------------------
% 0.21/0.49  % (12735)------------------------------
% 0.21/0.49  % (12739)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (12722)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (12733)Refutation not found, incomplete strategy% (12733)------------------------------
% 0.21/0.49  % (12733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (12733)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (12733)Memory used [KB]: 1663
% 0.21/0.49  % (12733)Time elapsed: 0.090 s
% 0.21/0.49  % (12733)------------------------------
% 0.21/0.49  % (12733)------------------------------
% 0.21/0.49  % (12739)Refutation not found, incomplete strategy% (12739)------------------------------
% 0.21/0.49  % (12739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (12739)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (12739)Memory used [KB]: 6140
% 0.21/0.49  % (12739)Time elapsed: 0.087 s
% 0.21/0.49  % (12739)------------------------------
% 0.21/0.49  % (12739)------------------------------
% 0.21/0.49  % (12720)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (12723)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (12720)Refutation not found, incomplete strategy% (12720)------------------------------
% 0.21/0.49  % (12720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (12720)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (12720)Memory used [KB]: 6140
% 0.21/0.49  % (12720)Time elapsed: 0.078 s
% 0.21/0.49  % (12720)------------------------------
% 0.21/0.49  % (12720)------------------------------
% 0.21/0.50  % (12723)Refutation not found, incomplete strategy% (12723)------------------------------
% 0.21/0.50  % (12723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12723)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12723)Memory used [KB]: 10618
% 0.21/0.50  % (12723)Time elapsed: 0.097 s
% 0.21/0.50  % (12723)------------------------------
% 0.21/0.50  % (12723)------------------------------
% 0.21/0.50  % (12738)Refutation not found, incomplete strategy% (12738)------------------------------
% 0.21/0.50  % (12738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12738)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12738)Memory used [KB]: 1791
% 0.21/0.50  % (12738)Time elapsed: 0.085 s
% 0.21/0.50  % (12738)------------------------------
% 0.21/0.50  % (12738)------------------------------
% 0.21/0.50  % (12729)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (12740)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (12725)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (12740)Refutation not found, incomplete strategy% (12740)------------------------------
% 0.21/0.50  % (12740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12740)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12740)Memory used [KB]: 10490
% 0.21/0.50  % (12740)Time elapsed: 0.096 s
% 0.21/0.50  % (12740)------------------------------
% 0.21/0.50  % (12740)------------------------------
% 0.21/0.50  % (12730)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (12729)Refutation not found, incomplete strategy% (12729)------------------------------
% 0.21/0.50  % (12729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12729)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12729)Memory used [KB]: 10618
% 0.21/0.50  % (12729)Time elapsed: 0.099 s
% 0.21/0.50  % (12729)------------------------------
% 0.21/0.50  % (12729)------------------------------
% 0.21/0.50  % (12722)Refutation not found, incomplete strategy% (12722)------------------------------
% 0.21/0.50  % (12722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12722)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12722)Memory used [KB]: 10746
% 0.21/0.50  % (12722)Time elapsed: 0.094 s
% 0.21/0.50  % (12722)------------------------------
% 0.21/0.50  % (12722)------------------------------
% 0.21/0.50  % (12730)Refutation not found, incomplete strategy% (12730)------------------------------
% 0.21/0.50  % (12730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12730)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12730)Memory used [KB]: 6140
% 0.21/0.50  % (12730)Time elapsed: 0.099 s
% 0.21/0.50  % (12730)------------------------------
% 0.21/0.50  % (12730)------------------------------
% 0.21/0.50  % (12737)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.50  % (12737)# SZS output start Saturation.
% 0.21/0.50  cnf(u23,negated_conjecture,
% 0.21/0.50      l1_struct_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u39,axiom,
% 0.21/0.50      ~l1_struct_0(X0) | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u22,negated_conjecture,
% 0.21/0.50      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u18,negated_conjecture,
% 0.21/0.50      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u31,axiom,
% 0.21/0.50      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u37,negated_conjecture,
% 0.21/0.50      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK2,X2) = k2_xboole_0(sK2,X2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u38,negated_conjecture,
% 0.21/0.50      ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X3) = k2_xboole_0(sK1,X3)).
% 0.21/0.50  
% 0.21/0.50  cnf(u26,axiom,
% 0.21/0.50      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.21/0.50  
% 0.21/0.50  cnf(u29,axiom,
% 0.21/0.50      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u30,axiom,
% 0.21/0.50      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u36,axiom,
% 0.21/0.50      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k4_subset_1(X1,X1,X0) = k2_xboole_0(X1,X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u20,negated_conjecture,
% 0.21/0.50      r1_xboole_0(sK1,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u28,axiom,
% 0.21/0.50      ~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0).
% 0.21/0.50  
% 0.21/0.50  cnf(u42,negated_conjecture,
% 0.21/0.50      sK2 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u43,negated_conjecture,
% 0.21/0.50      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u56,negated_conjecture,
% 0.21/0.50      sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u32,negated_conjecture,
% 0.21/0.50      sK1 = k4_xboole_0(sK1,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u50,negated_conjecture,
% 0.21/0.50      k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u19,negated_conjecture,
% 0.21/0.50      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u54,negated_conjecture,
% 0.21/0.50      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u35,negated_conjecture,
% 0.21/0.50      k7_subset_1(u1_struct_0(sK0),sK1,X3) = k4_xboole_0(sK1,X3)).
% 0.21/0.50  
% 0.21/0.50  cnf(u34,negated_conjecture,
% 0.21/0.50      k7_subset_1(u1_struct_0(sK0),sK2,X2) = k4_xboole_0(sK2,X2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u51,axiom,
% 0.21/0.50      k4_subset_1(X0,X0,X0) = k2_xboole_0(X0,X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u53,negated_conjecture,
% 0.21/0.50      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),sK1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u52,negated_conjecture,
% 0.21/0.50      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(u1_struct_0(sK0),sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u47,negated_conjecture,
% 0.21/0.50      k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,u1_struct_0(sK0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u49,negated_conjecture,
% 0.21/0.50      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u44,negated_conjecture,
% 0.21/0.50      k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k2_xboole_0(sK2,u1_struct_0(sK0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u46,negated_conjecture,
% 0.21/0.50      k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u45,negated_conjecture,
% 0.21/0.50      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u24,axiom,
% 0.21/0.50      k2_subset_1(X0) = X0).
% 0.21/0.50  
% 0.21/0.50  cnf(u33,axiom,
% 0.21/0.50      k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u27,axiom,
% 0.21/0.50      k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u21,negated_conjecture,
% 0.21/0.50      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.21/0.50  
% 0.21/0.50  % (12737)# SZS output end Saturation.
% 0.21/0.50  % (12737)------------------------------
% 0.21/0.50  % (12737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12737)Termination reason: Satisfiable
% 0.21/0.50  
% 0.21/0.50  % (12737)Memory used [KB]: 1663
% 0.21/0.50  % (12737)Time elapsed: 0.106 s
% 0.21/0.50  % (12737)------------------------------
% 0.21/0.50  % (12737)------------------------------
% 0.21/0.51  % (12719)Success in time 0.151 s
%------------------------------------------------------------------------------
