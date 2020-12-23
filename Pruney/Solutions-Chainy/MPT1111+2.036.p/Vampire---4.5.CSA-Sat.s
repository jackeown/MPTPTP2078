%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:14 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u24,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u23,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ r2_hidden(X2,k1_xboole_0) )).

cnf(u19,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK2(X0),X1)
    | k1_xboole_0 = X0 )).

cnf(u17,axiom,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 )).

cnf(u18,axiom,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2) )).

cnf(u22,negated_conjecture,
    ( k1_xboole_0 = sK1 )).

cnf(u25,negated_conjecture,
    ( k1_xboole_0 != k1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (9622)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (9623)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (9623)Refutation not found, incomplete strategy% (9623)------------------------------
% 0.21/0.47  % (9623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (9622)Refutation not found, incomplete strategy% (9622)------------------------------
% 0.21/0.47  % (9622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (9622)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (9622)Memory used [KB]: 10618
% 0.21/0.47  % (9622)Time elapsed: 0.051 s
% 0.21/0.47  % (9622)------------------------------
% 0.21/0.47  % (9622)------------------------------
% 0.21/0.47  % (9623)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (9623)Memory used [KB]: 6140
% 0.21/0.47  % (9623)Time elapsed: 0.004 s
% 0.21/0.47  % (9623)------------------------------
% 0.21/0.47  % (9623)------------------------------
% 0.21/0.47  % (9614)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (9615)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (9614)Refutation not found, incomplete strategy% (9614)------------------------------
% 0.21/0.47  % (9614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (9614)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (9614)Memory used [KB]: 10618
% 0.21/0.47  % (9614)Time elapsed: 0.063 s
% 0.21/0.47  % (9614)------------------------------
% 0.21/0.47  % (9614)------------------------------
% 0.21/0.47  % (9612)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (9627)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % (9608)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (9608)Refutation not found, incomplete strategy% (9608)------------------------------
% 0.21/0.48  % (9608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9608)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (9608)Memory used [KB]: 10618
% 0.21/0.48  % (9608)Time elapsed: 0.074 s
% 0.21/0.48  % (9608)------------------------------
% 0.21/0.48  % (9608)------------------------------
% 0.21/0.48  % (9607)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (9607)Refutation not found, incomplete strategy% (9607)------------------------------
% 0.21/0.48  % (9607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9607)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (9607)Memory used [KB]: 6012
% 0.21/0.48  % (9607)Time elapsed: 0.076 s
% 0.21/0.48  % (9607)------------------------------
% 0.21/0.48  % (9607)------------------------------
% 0.21/0.48  % (9609)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (9625)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (9617)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (9609)Refutation not found, incomplete strategy% (9609)------------------------------
% 0.21/0.49  % (9609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9609)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (9609)Memory used [KB]: 10618
% 0.21/0.49  % (9609)Time elapsed: 0.074 s
% 0.21/0.49  % (9609)------------------------------
% 0.21/0.49  % (9609)------------------------------
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (9625)# SZS output start Saturation.
% 0.21/0.49  cnf(u24,negated_conjecture,
% 0.21/0.49      m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.49  
% 0.21/0.49  cnf(u23,negated_conjecture,
% 0.21/0.49      ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,k1_xboole_0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u19,axiom,
% 0.21/0.49      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK2(X0),X1) | k1_xboole_0 = X0).
% 0.21/0.49  
% 0.21/0.49  cnf(u17,axiom,
% 0.21/0.49      r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0).
% 0.21/0.49  
% 0.21/0.49  cnf(u18,axiom,
% 0.21/0.49      ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u22,negated_conjecture,
% 0.21/0.49      k1_xboole_0 = sK1).
% 0.21/0.49  
% 0.21/0.49  cnf(u25,negated_conjecture,
% 0.21/0.49      k1_xboole_0 != k1_struct_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  % (9625)# SZS output end Saturation.
% 0.21/0.49  % (9625)------------------------------
% 0.21/0.49  % (9625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9625)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (9625)Memory used [KB]: 1663
% 0.21/0.49  % (9625)Time elapsed: 0.078 s
% 0.21/0.49  % (9625)------------------------------
% 0.21/0.49  % (9625)------------------------------
% 0.21/0.49  % (9604)Success in time 0.128 s
%------------------------------------------------------------------------------
