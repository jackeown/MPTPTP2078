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
% DateTime   : Thu Dec  3 13:09:14 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (3689)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (3698)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (3690)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (3691)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (3690)Refutation not found, incomplete strategy% (3690)------------------------------
% 0.20/0.50  % (3690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3690)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (3690)Memory used [KB]: 10618
% 0.20/0.50  % (3690)Time elapsed: 0.067 s
% 0.20/0.50  % (3690)------------------------------
% 0.20/0.50  % (3690)------------------------------
% 0.20/0.50  % (3698)Refutation not found, incomplete strategy% (3698)------------------------------
% 0.20/0.50  % (3698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3698)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (3698)Memory used [KB]: 10618
% 0.20/0.50  % (3698)Time elapsed: 0.082 s
% 0.20/0.50  % (3698)------------------------------
% 0.20/0.50  % (3698)------------------------------
% 0.20/0.50  % (3697)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (3697)Refutation not found, incomplete strategy% (3697)------------------------------
% 0.20/0.50  % (3697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3697)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (3697)Memory used [KB]: 1663
% 0.20/0.50  % (3697)Time elapsed: 0.075 s
% 0.20/0.50  % (3697)------------------------------
% 0.20/0.50  % (3697)------------------------------
% 0.20/0.51  % (3699)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (3699)Refutation not found, incomplete strategy% (3699)------------------------------
% 0.20/0.51  % (3699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3699)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (3699)Memory used [KB]: 6140
% 0.20/0.51  % (3699)Time elapsed: 0.088 s
% 0.20/0.51  % (3699)------------------------------
% 0.20/0.51  % (3699)------------------------------
% 0.20/0.52  % (3701)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.52  % (3701)# SZS output start Saturation.
% 0.20/0.52  cnf(u24,negated_conjecture,
% 0.20/0.52      m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.52  
% 0.20/0.52  cnf(u23,negated_conjecture,
% 0.20/0.52      ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,k1_xboole_0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u19,axiom,
% 0.20/0.52      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK2(X0),X1) | k1_xboole_0 = X0).
% 0.20/0.52  
% 0.20/0.52  cnf(u17,axiom,
% 0.20/0.52      r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0).
% 0.20/0.52  
% 0.20/0.52  cnf(u18,axiom,
% 0.20/0.52      ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u22,negated_conjecture,
% 0.20/0.52      k1_xboole_0 = sK1).
% 0.20/0.52  
% 0.20/0.52  cnf(u25,negated_conjecture,
% 0.20/0.52      k1_xboole_0 != k1_struct_0(sK0)).
% 0.20/0.52  
% 0.20/0.52  % (3701)# SZS output end Saturation.
% 0.20/0.52  % (3701)------------------------------
% 0.20/0.52  % (3701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (3701)Termination reason: Satisfiable
% 0.20/0.52  
% 0.20/0.52  % (3701)Memory used [KB]: 1663
% 0.20/0.52  % (3701)Time elapsed: 0.061 s
% 0.20/0.52  % (3701)------------------------------
% 0.20/0.52  % (3701)------------------------------
% 0.20/0.52  % (3683)Success in time 0.158 s
%------------------------------------------------------------------------------
