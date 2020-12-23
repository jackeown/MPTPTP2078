%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:28 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    5 (   5 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    0
%              Number of atoms          :    6 (   6 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u22,negated_conjecture,(
    u1_struct_0(sK0) != k2_struct_0(sK0) )).

tff(u21,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u20,negated_conjecture,(
    u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) )).

tff(u19,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 ) )).

tff(u18,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:58:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (404)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.43  % (397)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.43  % (397)Refutation not found, incomplete strategy% (397)------------------------------
% 0.21/0.43  % (397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (397)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.43  
% 0.21/0.43  % (397)Memory used [KB]: 10490
% 0.21/0.43  % (397)Time elapsed: 0.004 s
% 0.21/0.43  % (397)------------------------------
% 0.21/0.43  % (397)------------------------------
% 0.21/0.43  % (405)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.44  % (403)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.45  % (407)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.46  % (398)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.46  % (398)# SZS output start Saturation.
% 0.21/0.46  tff(u22,negated_conjecture,
% 0.21/0.46      (u1_struct_0(sK0) != k2_struct_0(sK0))).
% 0.21/0.46  
% 0.21/0.46  tff(u21,axiom,
% 0.21/0.46      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.21/0.46  
% 0.21/0.46  tff(u20,negated_conjecture,
% 0.21/0.46      (u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)))).
% 0.21/0.46  
% 0.21/0.46  tff(u19,axiom,
% 0.21/0.46      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u18,negated_conjecture,
% 0.21/0.46      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.46  
% 0.21/0.46  % (398)# SZS output end Saturation.
% 0.21/0.46  % (398)------------------------------
% 0.21/0.46  % (398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (398)Termination reason: Satisfiable
% 0.21/0.46  
% 0.21/0.46  % (398)Memory used [KB]: 6012
% 0.21/0.46  % (398)Time elapsed: 0.041 s
% 0.21/0.46  % (398)------------------------------
% 0.21/0.46  % (398)------------------------------
% 0.21/0.46  % (392)Success in time 0.094 s
%------------------------------------------------------------------------------
