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
% DateTime   : Thu Dec  3 13:16:20 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :    1 (   1 expanded)
%              Number of leaves         :    1 (   1 expanded)
%              Depth                    :    0
%              Number of atoms          :    1 (   1 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    2 (   2 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u12,negated_conjecture,(
    k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n008.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 17:22:30 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (20678)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (20686)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.51  % (20673)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (20673)Refutation not found, incomplete strategy% (20673)------------------------------
% 0.22/0.51  % (20673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20673)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (20673)Memory used [KB]: 6140
% 0.22/0.51  % (20673)Time elapsed: 0.098 s
% 0.22/0.51  % (20673)------------------------------
% 0.22/0.51  % (20673)------------------------------
% 0.22/0.51  % (20678)Refutation not found, incomplete strategy% (20678)------------------------------
% 0.22/0.51  % (20678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20678)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (20678)Memory used [KB]: 10618
% 0.22/0.51  % (20678)Time elapsed: 0.092 s
% 0.22/0.51  % (20678)------------------------------
% 0.22/0.51  % (20678)------------------------------
% 0.22/0.51  % (20694)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.51  % (20694)Refutation not found, incomplete strategy% (20694)------------------------------
% 0.22/0.51  % (20694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20694)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (20694)Memory used [KB]: 6140
% 0.22/0.51  % (20694)Time elapsed: 0.096 s
% 0.22/0.51  % (20694)------------------------------
% 0.22/0.51  % (20694)------------------------------
% 0.22/0.52  % (20686)Refutation not found, incomplete strategy% (20686)------------------------------
% 0.22/0.52  % (20686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20686)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20686)Memory used [KB]: 10618
% 0.22/0.52  % (20686)Time elapsed: 0.106 s
% 0.22/0.52  % (20686)------------------------------
% 0.22/0.52  % (20686)------------------------------
% 0.22/0.52  % (20682)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (20672)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.53  % (20672)# SZS output start Saturation.
% 0.22/0.53  tff(u12,negated_conjecture,
% 0.22/0.53      (k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))))).
% 0.22/0.53  
% 0.22/0.53  % (20672)# SZS output end Saturation.
% 0.22/0.53  % (20672)------------------------------
% 0.22/0.53  % (20672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20672)Termination reason: Satisfiable
% 0.22/0.53  
% 0.22/0.53  % (20672)Memory used [KB]: 10618
% 0.22/0.53  % (20672)Time elapsed: 0.119 s
% 0.22/0.53  % (20672)------------------------------
% 0.22/0.53  % (20672)------------------------------
% 0.22/0.53  % (20669)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (20669)Refutation not found, incomplete strategy% (20669)------------------------------
% 0.22/0.53  % (20669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20669)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (20669)Memory used [KB]: 1663
% 0.22/0.53  % (20669)Time elapsed: 0.115 s
% 0.22/0.53  % (20669)------------------------------
% 0.22/0.53  % (20669)------------------------------
% 0.22/0.53  % (20697)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (20696)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.53  % (20696)Refutation not found, incomplete strategy% (20696)------------------------------
% 1.32/0.53  % (20696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (20696)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (20696)Memory used [KB]: 6140
% 1.32/0.53  % (20696)Time elapsed: 0.122 s
% 1.32/0.53  % (20696)------------------------------
% 1.32/0.53  % (20696)------------------------------
% 1.32/0.53  % (20671)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.53  % (20671)Refutation not found, incomplete strategy% (20671)------------------------------
% 1.32/0.53  % (20671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (20671)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (20671)Memory used [KB]: 10618
% 1.32/0.53  % (20671)Time elapsed: 0.118 s
% 1.32/0.53  % (20671)------------------------------
% 1.32/0.53  % (20671)------------------------------
% 1.32/0.53  % (20693)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.54  % (20689)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.54  % (20674)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.32/0.54  % (20689)Refutation not found, incomplete strategy% (20689)------------------------------
% 1.32/0.54  % (20689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (20689)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (20689)Memory used [KB]: 10618
% 1.32/0.54  % (20689)Time elapsed: 0.130 s
% 1.32/0.54  % (20689)------------------------------
% 1.32/0.54  % (20689)------------------------------
% 1.32/0.54  % (20666)Success in time 0.172 s
%------------------------------------------------------------------------------
