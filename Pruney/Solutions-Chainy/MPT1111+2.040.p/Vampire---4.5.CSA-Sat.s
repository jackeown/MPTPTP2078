%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:14 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    0
%              Number of atoms          :   23 (  23 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u29,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u28,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ r2_hidden(X2,k1_xboole_0) )).

cnf(u20,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK2(X0),X1)
    | k1_xboole_0 = X0 )).

cnf(u18,axiom,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 )).

cnf(u19,axiom,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2) )).

cnf(u16,axiom,
    ( ~ r2_hidden(X2,X0)
    | k1_xboole_0 = X0
    | k4_tarski(X2,X3) != sK2(X0) )).

cnf(u17,axiom,
    ( ~ r2_hidden(X3,X0)
    | k1_xboole_0 = X0
    | k4_tarski(X2,X3) != sK2(X0) )).

cnf(u27,negated_conjecture,
    ( k1_xboole_0 = sK1 )).

cnf(u30,negated_conjecture,
    ( k1_xboole_0 != k1_struct_0(sK0) )).

cnf(u24,axiom,
    ( sK2(X0) != k4_tarski(X1,sK2(X0))
    | k1_xboole_0 = X0 )).

cnf(u22,axiom,
    ( sK2(X0) != k4_tarski(sK2(X0),X1)
    | k1_xboole_0 = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (880)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (877)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (895)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  % (877)Refutation not found, incomplete strategy% (877)------------------------------
% 0.21/0.49  % (877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (877)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (877)Memory used [KB]: 10618
% 0.21/0.49  % (877)Time elapsed: 0.069 s
% 0.21/0.49  % (877)------------------------------
% 0.21/0.49  % (877)------------------------------
% 0.21/0.50  % (895)Refutation not found, incomplete strategy% (895)------------------------------
% 0.21/0.50  % (895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (895)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (895)Memory used [KB]: 1663
% 0.21/0.50  % (895)Time elapsed: 0.078 s
% 0.21/0.50  % (895)------------------------------
% 0.21/0.50  % (895)------------------------------
% 0.21/0.51  % (881)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (896)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (878)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (878)Refutation not found, incomplete strategy% (878)------------------------------
% 0.21/0.52  % (878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (878)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (878)Memory used [KB]: 10618
% 0.21/0.52  % (878)Time elapsed: 0.081 s
% 0.21/0.52  % (878)------------------------------
% 0.21/0.52  % (878)------------------------------
% 0.21/0.52  % (891)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (881)Refutation not found, incomplete strategy% (881)------------------------------
% 0.21/0.52  % (881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (881)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (881)Memory used [KB]: 10618
% 0.21/0.52  % (881)Time elapsed: 0.066 s
% 0.21/0.52  % (881)------------------------------
% 0.21/0.52  % (881)------------------------------
% 0.21/0.52  % (891)Refutation not found, incomplete strategy% (891)------------------------------
% 0.21/0.52  % (891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (891)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (891)Memory used [KB]: 10618
% 0.21/0.52  % (891)Time elapsed: 0.088 s
% 0.21/0.52  % (891)------------------------------
% 0.21/0.52  % (891)------------------------------
% 0.21/0.53  % (887)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.53  % (887)Refutation not found, incomplete strategy% (887)------------------------------
% 0.21/0.53  % (887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (887)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (887)Memory used [KB]: 10490
% 0.21/0.53  % (887)Time elapsed: 0.105 s
% 0.21/0.53  % (887)------------------------------
% 0.21/0.53  % (887)------------------------------
% 0.21/0.53  % (888)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (888)Refutation not found, incomplete strategy% (888)------------------------------
% 0.21/0.54  % (888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (888)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (888)Memory used [KB]: 6012
% 0.21/0.54  % (888)Time elapsed: 0.002 s
% 0.21/0.54  % (888)------------------------------
% 0.21/0.54  % (888)------------------------------
% 0.21/0.54  % (879)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.54  % (894)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.54  % (894)# SZS output start Saturation.
% 0.21/0.54  cnf(u29,negated_conjecture,
% 0.21/0.54      m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u28,negated_conjecture,
% 0.21/0.54      ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,k1_xboole_0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u20,axiom,
% 0.21/0.54      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK2(X0),X1) | k1_xboole_0 = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u18,axiom,
% 0.21/0.54      r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u19,axiom,
% 0.21/0.54      ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u16,axiom,
% 0.21/0.54      ~r2_hidden(X2,X0) | k1_xboole_0 = X0 | k4_tarski(X2,X3) != sK2(X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u17,axiom,
% 0.21/0.54      ~r2_hidden(X3,X0) | k1_xboole_0 = X0 | k4_tarski(X2,X3) != sK2(X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u27,negated_conjecture,
% 0.21/0.54      k1_xboole_0 = sK1).
% 0.21/0.54  
% 0.21/0.54  cnf(u30,negated_conjecture,
% 0.21/0.54      k1_xboole_0 != k1_struct_0(sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u24,axiom,
% 0.21/0.54      sK2(X0) != k4_tarski(X1,sK2(X0)) | k1_xboole_0 = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u22,axiom,
% 0.21/0.54      sK2(X0) != k4_tarski(sK2(X0),X1) | k1_xboole_0 = X0).
% 0.21/0.54  
% 0.21/0.54  % (894)# SZS output end Saturation.
% 0.21/0.54  % (894)------------------------------
% 0.21/0.54  % (894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (894)Termination reason: Satisfiable
% 0.21/0.54  
% 0.21/0.54  % (894)Memory used [KB]: 1663
% 0.21/0.54  % (894)Time elapsed: 0.125 s
% 0.21/0.54  % (894)------------------------------
% 0.21/0.54  % (894)------------------------------
% 0.21/0.54  % (869)Success in time 0.183 s
%------------------------------------------------------------------------------
