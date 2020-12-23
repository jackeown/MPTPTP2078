%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:25 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :    1 (   1 expanded)
%              Number of leaves         :    1 (   1 expanded)
%              Depth                    :    0
%              Number of atoms          :    1 (   1 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    2 (   2 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u21,negated_conjecture,(
    k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:23:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (27077)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (27082)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (27093)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.52  % (27071)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.52  % (27071)# SZS output start Saturation.
% 0.22/0.52  tff(u21,negated_conjecture,
% 0.22/0.52      (k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2))).
% 0.22/0.52  
% 0.22/0.52  % (27071)# SZS output end Saturation.
% 0.22/0.52  % (27071)------------------------------
% 0.22/0.52  % (27071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (27071)Termination reason: Satisfiable
% 0.22/0.52  
% 0.22/0.52  % (27071)Memory used [KB]: 10618
% 0.22/0.52  % (27071)Time elapsed: 0.098 s
% 0.22/0.52  % (27071)------------------------------
% 0.22/0.52  % (27071)------------------------------
% 0.22/0.52  % (27074)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (27085)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.52  % (27077)Refutation not found, incomplete strategy% (27077)------------------------------
% 0.22/0.52  % (27077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (27077)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (27077)Memory used [KB]: 10618
% 0.22/0.52  % (27077)Time elapsed: 0.103 s
% 0.22/0.52  % (27077)------------------------------
% 0.22/0.52  % (27077)------------------------------
% 0.22/0.53  % (27093)Refutation not found, incomplete strategy% (27093)------------------------------
% 0.22/0.53  % (27093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (27093)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (27093)Memory used [KB]: 6140
% 0.22/0.53  % (27093)Time elapsed: 0.103 s
% 0.22/0.53  % (27093)------------------------------
% 0.22/0.53  % (27093)------------------------------
% 0.22/0.53  % (27068)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (27085)Refutation not found, incomplete strategy% (27085)------------------------------
% 0.22/0.53  % (27085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (27085)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (27085)Memory used [KB]: 10618
% 0.22/0.53  % (27085)Time elapsed: 0.103 s
% 0.22/0.53  % (27085)------------------------------
% 0.22/0.53  % (27085)------------------------------
% 0.22/0.53  % (27068)Refutation not found, incomplete strategy% (27068)------------------------------
% 0.22/0.53  % (27068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (27068)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (27068)Memory used [KB]: 1663
% 0.22/0.53  % (27068)Time elapsed: 0.105 s
% 0.22/0.53  % (27068)------------------------------
% 0.22/0.53  % (27068)------------------------------
% 0.22/0.53  % (27069)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.37/0.53  % (27083)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.37/0.53  % (27070)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.37/0.54  % (27083)Refutation not found, incomplete strategy% (27083)------------------------------
% 1.37/0.54  % (27083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (27083)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (27083)Memory used [KB]: 6140
% 1.37/0.54  % (27083)Time elapsed: 0.001 s
% 1.37/0.54  % (27083)------------------------------
% 1.37/0.54  % (27083)------------------------------
% 1.37/0.54  % (27097)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.37/0.54  % (27070)Refutation not found, incomplete strategy% (27070)------------------------------
% 1.37/0.54  % (27070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (27070)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (27070)Memory used [KB]: 10618
% 1.37/0.54  % (27070)Time elapsed: 0.115 s
% 1.37/0.54  % (27070)------------------------------
% 1.37/0.54  % (27070)------------------------------
% 1.37/0.54  % (27067)Success in time 0.17 s
%------------------------------------------------------------------------------
