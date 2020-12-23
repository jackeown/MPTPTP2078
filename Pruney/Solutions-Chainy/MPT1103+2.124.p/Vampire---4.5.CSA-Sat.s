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
% DateTime   : Thu Dec  3 13:08:50 EST 2020

% Result     : CounterSatisfiable 1.55s
% Output     : Saturation 1.55s
% Verified   : 
% Statistics : Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    0
%              Number of atoms          :   19 (  19 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u14,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u17,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u24,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u19,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u26,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u25,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u23,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u16,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u11,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u22,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u21,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:03:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.21/0.54  % (3339)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.21/0.55  % (3360)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.21/0.56  % (3339)Refutation not found, incomplete strategy% (3339)------------------------------
% 1.21/0.56  % (3339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.56  % (3352)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.21/0.56  % (3352)Refutation not found, incomplete strategy% (3352)------------------------------
% 1.21/0.56  % (3352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (3360)Refutation not found, incomplete strategy% (3360)------------------------------
% 1.55/0.56  % (3360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (3360)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (3360)Memory used [KB]: 1663
% 1.55/0.56  % (3360)Time elapsed: 0.077 s
% 1.55/0.56  % (3360)------------------------------
% 1.55/0.56  % (3360)------------------------------
% 1.55/0.56  % (3352)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (3352)Memory used [KB]: 6140
% 1.55/0.56  % (3352)Time elapsed: 0.004 s
% 1.55/0.56  % (3352)------------------------------
% 1.55/0.56  % (3352)------------------------------
% 1.55/0.56  % (3339)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (3339)Memory used [KB]: 10618
% 1.55/0.56  % (3339)Time elapsed: 0.128 s
% 1.55/0.56  % (3339)------------------------------
% 1.55/0.56  % (3339)------------------------------
% 1.55/0.57  % (3344)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.55/0.57  % (3343)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.55/0.57  % (3347)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.55/0.57  % SZS status CounterSatisfiable for theBenchmark
% 1.55/0.57  % (3343)# SZS output start Saturation.
% 1.55/0.57  cnf(u14,negated_conjecture,
% 1.55/0.57      l1_struct_0(sK0)).
% 1.55/0.57  
% 1.55/0.57  cnf(u17,axiom,
% 1.55/0.57      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 1.55/0.57  
% 1.55/0.57  cnf(u13,negated_conjecture,
% 1.55/0.57      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.55/0.57  
% 1.55/0.57  cnf(u24,negated_conjecture,
% 1.55/0.57      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 1.55/0.57  
% 1.55/0.57  cnf(u19,axiom,
% 1.55/0.57      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 1.55/0.57  
% 1.55/0.57  cnf(u26,negated_conjecture,
% 1.55/0.57      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 1.55/0.57  
% 1.55/0.57  cnf(u25,negated_conjecture,
% 1.55/0.57      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 1.55/0.57  
% 1.55/0.57  cnf(u23,negated_conjecture,
% 1.55/0.57      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 1.55/0.57  
% 1.55/0.57  cnf(u16,axiom,
% 1.55/0.57      k4_xboole_0(X0,k1_xboole_0) = X0).
% 1.55/0.57  
% 1.55/0.57  cnf(u11,negated_conjecture,
% 1.55/0.57      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 1.55/0.57  
% 1.55/0.57  cnf(u22,axiom,
% 1.55/0.57      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 1.55/0.57  
% 1.55/0.57  cnf(u21,negated_conjecture,
% 1.55/0.57      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.55/0.57  
% 1.55/0.57  % (3343)# SZS output end Saturation.
% 1.55/0.57  % (3343)------------------------------
% 1.55/0.57  % (3343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (3343)Termination reason: Satisfiable
% 1.55/0.57  
% 1.55/0.57  % (3343)Memory used [KB]: 6140
% 1.55/0.57  % (3343)Time elapsed: 0.151 s
% 1.55/0.57  % (3343)------------------------------
% 1.55/0.57  % (3343)------------------------------
% 1.55/0.57  % (3355)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.55/0.57  % (3336)Success in time 0.211 s
%------------------------------------------------------------------------------
