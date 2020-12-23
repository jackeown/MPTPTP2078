%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:56 EST 2020

% Result     : CounterSatisfiable 1.43s
% Output     : Saturation 1.43s
% Verified   : 
% Statistics : Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    0
%              Number of atoms          :   21 (  21 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u27,negated_conjecture,
    ( m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r2_hidden(X0,sK1) )).

cnf(u12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u20,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2) )).

cnf(u18,axiom,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_tarski(X0,X1) )).

cnf(u17,axiom,
    ( ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1)
    | ~ r1_tarski(X0,X1) )).

cnf(u19,axiom,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | r1_tarski(X0,X1) )).

cnf(u21,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u16,axiom,
    ( ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 )).

cnf(u26,axiom,
    ( ~ r1_tarski(X0,X2)
    | r2_hidden(sK2(X0,X1),X2)
    | r1_tarski(X0,X1) )).

cnf(u13,negated_conjecture,
    ( k3_waybel_0(sK0,sK1) != a_2_0_waybel_0(sK0,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:32:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (12707)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (12704)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (12704)Refutation not found, incomplete strategy% (12704)------------------------------
% 0.21/0.53  % (12704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12704)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12704)Memory used [KB]: 6140
% 0.21/0.53  % (12704)Time elapsed: 0.106 s
% 0.21/0.53  % (12704)------------------------------
% 0.21/0.53  % (12704)------------------------------
% 0.21/0.53  % (12699)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (12699)Refutation not found, incomplete strategy% (12699)------------------------------
% 0.21/0.53  % (12699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12699)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12699)Memory used [KB]: 10618
% 0.21/0.53  % (12699)Time elapsed: 0.117 s
% 0.21/0.53  % (12699)------------------------------
% 0.21/0.53  % (12699)------------------------------
% 0.21/0.53  % (12710)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (12697)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (12697)Refutation not found, incomplete strategy% (12697)------------------------------
% 0.21/0.53  % (12697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12697)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12697)Memory used [KB]: 1663
% 0.21/0.53  % (12697)Time elapsed: 0.115 s
% 0.21/0.53  % (12697)------------------------------
% 0.21/0.53  % (12697)------------------------------
% 0.21/0.53  % (12712)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (12700)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (12721)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (12715)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (12720)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (12720)Refutation not found, incomplete strategy% (12720)------------------------------
% 0.21/0.54  % (12720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12720)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12720)Memory used [KB]: 1663
% 0.21/0.54  % (12720)Time elapsed: 0.129 s
% 0.21/0.54  % (12720)------------------------------
% 0.21/0.54  % (12720)------------------------------
% 0.21/0.54  % (12707)Refutation not found, incomplete strategy% (12707)------------------------------
% 0.21/0.54  % (12707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12707)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12707)Memory used [KB]: 10618
% 0.21/0.54  % (12707)Time elapsed: 0.126 s
% 0.21/0.54  % (12707)------------------------------
% 0.21/0.54  % (12707)------------------------------
% 0.21/0.54  % (12708)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (12708)Refutation not found, incomplete strategy% (12708)------------------------------
% 0.21/0.54  % (12708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12708)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12708)Memory used [KB]: 10618
% 0.21/0.54  % (12708)Time elapsed: 0.126 s
% 0.21/0.54  % (12708)------------------------------
% 0.21/0.54  % (12708)------------------------------
% 0.21/0.54  % (12711)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (12723)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (12702)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (12724)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (12723)Refutation not found, incomplete strategy% (12723)------------------------------
% 0.21/0.54  % (12723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12723)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12723)Memory used [KB]: 10618
% 0.21/0.54  % (12723)Time elapsed: 0.099 s
% 0.21/0.54  % (12723)------------------------------
% 0.21/0.54  % (12723)------------------------------
% 0.21/0.54  % (12702)Refutation not found, incomplete strategy% (12702)------------------------------
% 0.21/0.54  % (12702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12702)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12702)Memory used [KB]: 6140
% 0.21/0.54  % (12702)Time elapsed: 0.122 s
% 0.21/0.54  % (12702)------------------------------
% 0.21/0.54  % (12702)------------------------------
% 1.43/0.54  % (12714)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.43/0.54  % (12718)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.54  % (12701)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.43/0.55  % (12718)Refutation not found, incomplete strategy% (12718)------------------------------
% 1.43/0.55  % (12718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (12718)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (12718)Memory used [KB]: 1663
% 1.43/0.55  % (12718)Time elapsed: 0.139 s
% 1.43/0.55  % (12718)------------------------------
% 1.43/0.55  % (12718)------------------------------
% 1.43/0.55  % (12701)Refutation not found, incomplete strategy% (12701)------------------------------
% 1.43/0.55  % (12701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (12701)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (12701)Memory used [KB]: 6140
% 1.43/0.55  % (12701)Time elapsed: 0.103 s
% 1.43/0.55  % (12701)------------------------------
% 1.43/0.55  % (12701)------------------------------
% 1.43/0.55  % (12703)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.43/0.55  % (12719)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.43/0.55  % SZS status CounterSatisfiable for theBenchmark
% 1.43/0.55  % (12703)# SZS output start Saturation.
% 1.43/0.55  cnf(u27,negated_conjecture,
% 1.43/0.55      m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1)).
% 1.43/0.55  
% 1.43/0.55  cnf(u12,negated_conjecture,
% 1.43/0.55      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.43/0.55  
% 1.43/0.55  cnf(u20,axiom,
% 1.43/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)).
% 1.43/0.55  
% 1.43/0.55  cnf(u18,axiom,
% 1.43/0.55      r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)).
% 1.43/0.55  
% 1.43/0.55  cnf(u17,axiom,
% 1.43/0.55      ~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)).
% 1.43/0.55  
% 1.43/0.55  cnf(u19,axiom,
% 1.43/0.55      ~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)).
% 1.43/0.55  
% 1.43/0.55  cnf(u21,axiom,
% 1.43/0.55      r1_tarski(X1,X1)).
% 1.43/0.55  
% 1.43/0.55  cnf(u16,axiom,
% 1.43/0.55      ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1).
% 1.43/0.55  
% 1.43/0.55  cnf(u26,axiom,
% 1.43/0.55      ~r1_tarski(X0,X2) | r2_hidden(sK2(X0,X1),X2) | r1_tarski(X0,X1)).
% 1.43/0.55  
% 1.43/0.55  cnf(u13,negated_conjecture,
% 1.43/0.55      k3_waybel_0(sK0,sK1) != a_2_0_waybel_0(sK0,sK1)).
% 1.43/0.55  
% 1.43/0.55  % (12703)# SZS output end Saturation.
% 1.43/0.55  % (12703)------------------------------
% 1.43/0.55  % (12703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (12703)Termination reason: Satisfiable
% 1.43/0.55  
% 1.43/0.55  % (12703)Memory used [KB]: 6140
% 1.43/0.55  % (12703)Time elapsed: 0.140 s
% 1.43/0.55  % (12703)------------------------------
% 1.43/0.55  % (12703)------------------------------
% 1.43/0.55  % (12696)Success in time 0.185 s
%------------------------------------------------------------------------------
