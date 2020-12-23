%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:22 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    0
%              Number of atoms          :   42 (  42 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (32330)Memory used [KB]: 9850
% (32330)Time elapsed: 0.092 s
% (32330)------------------------------
% (32330)------------------------------
tff(u70,negated_conjecture,
    ( ~ ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK2) )).

tff(u69,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_xboole_0(u1_struct_0(sK1)) )).

tff(u68,axiom,(
    ! [X1,X0,X2] :
      ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_pre_topc(X2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_xboole_0(X0)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ) )).

tff(u67,negated_conjecture,(
    ~ m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u66,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u65,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) )).

tff(u64,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) )).

tff(u63,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) )).

tff(u62,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u61,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) )).

tff(u60,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X0,X2)
      | m1_subset_1(X0,X1)
      | ~ v1_xboole_0(X2)
      | ~ v1_xboole_0(k1_zfmisc_1(X1)) ) )).

tff(u59,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u58,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK1))
    | r2_hidden(sK2,u1_struct_0(sK1)) )).

tff(u57,negated_conjecture,(
    l1_pre_topc(sK0) )).

tff(u56,negated_conjecture,(
    l1_pre_topc(sK1) )).

tff(u55,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) )).

tff(u54,negated_conjecture,(
    m1_pre_topc(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:47:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (32328)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.22/0.47  % (32331)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.49  % (32339)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.49  % (32336)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.50  % (32336)Refutation not found, incomplete strategy% (32336)------------------------------
% 0.22/0.50  % (32336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (32336)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (32336)Memory used [KB]: 9850
% 0.22/0.50  % (32336)Time elapsed: 0.083 s
% 0.22/0.50  % (32336)------------------------------
% 0.22/0.50  % (32336)------------------------------
% 0.22/0.50  % (32340)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.50  % (32341)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.50  % (32341)Refutation not found, incomplete strategy% (32341)------------------------------
% 0.22/0.50  % (32341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (32341)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (32341)Memory used [KB]: 5373
% 0.22/0.50  % (32341)Time elapsed: 0.091 s
% 0.22/0.50  % (32341)------------------------------
% 0.22/0.50  % (32341)------------------------------
% 0.22/0.50  % (32342)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.50  % (32330)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.50  % (32327)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.50  % (32342)Refutation not found, incomplete strategy% (32342)------------------------------
% 0.22/0.50  % (32342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (32342)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (32342)Memory used [KB]: 895
% 0.22/0.50  % (32342)Time elapsed: 0.058 s
% 0.22/0.50  % (32342)------------------------------
% 0.22/0.50  % (32342)------------------------------
% 0.22/0.50  % (32334)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.51  % (32327)Refutation not found, incomplete strategy% (32327)------------------------------
% 0.22/0.51  % (32327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (32327)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (32327)Memory used [KB]: 5373
% 0.22/0.51  % (32327)Time elapsed: 0.089 s
% 0.22/0.51  % (32327)------------------------------
% 0.22/0.51  % (32327)------------------------------
% 0.22/0.51  % (32330)Refutation not found, incomplete strategy% (32330)------------------------------
% 0.22/0.51  % (32330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (32330)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (32334)# SZS output start Saturation.
% 0.22/0.51  % (32330)Memory used [KB]: 9850
% 0.22/0.51  % (32330)Time elapsed: 0.092 s
% 0.22/0.51  % (32330)------------------------------
% 0.22/0.51  % (32330)------------------------------
% 0.22/0.51  tff(u70,negated_conjecture,
% 0.22/0.51      ((~~v1_xboole_0(sK2)) | ~v1_xboole_0(sK2))).
% 0.22/0.51  
% 0.22/0.51  tff(u69,negated_conjecture,
% 0.22/0.51      ((~~v1_xboole_0(u1_struct_0(sK1))) | ~v1_xboole_0(u1_struct_0(sK1)))).
% 0.22/0.51  
% 0.22/0.51  tff(u68,axiom,
% 0.22/0.51      (![X1, X0, X2] : ((~v1_xboole_0(k1_zfmisc_1(u1_struct_0(X2))) | ~m1_pre_topc(X2,X1) | ~l1_pre_topc(X1) | ~v1_xboole_0(X0) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))))))).
% 0.22/0.51  
% 0.22/0.51  tff(u67,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.22/0.51  
% 0.22/0.51  tff(u66,axiom,
% 0.22/0.51      (![X1, X0] : ((~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u65,axiom,
% 0.22/0.51      (![X1, X0] : ((~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u64,axiom,
% 0.22/0.51      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1))))).
% 0.22/0.51  
% 0.22/0.51  tff(u63,axiom,
% 0.22/0.51      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u62,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.22/0.51  
% 0.22/0.51  tff(u61,axiom,
% 0.22/0.51      (![X1, X0] : ((m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u60,axiom,
% 0.22/0.51      (![X1, X0, X2] : ((~r2_hidden(X0,X2) | m1_subset_1(X0,X1) | ~v1_xboole_0(X2) | ~v1_xboole_0(k1_zfmisc_1(X1)))))).
% 0.22/0.51  
% 0.22/0.51  tff(u59,axiom,
% 0.22/0.51      (![X1, X0] : ((~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u58,negated_conjecture,
% 0.22/0.51      ((~~v1_xboole_0(u1_struct_0(sK1))) | r2_hidden(sK2,u1_struct_0(sK1)))).
% 0.22/0.51  
% 0.22/0.51  tff(u57,negated_conjecture,
% 0.22/0.51      l1_pre_topc(sK0)).
% 0.22/0.51  
% 0.22/0.51  tff(u56,negated_conjecture,
% 0.22/0.51      l1_pre_topc(sK1)).
% 0.22/0.51  
% 0.22/0.51  tff(u55,axiom,
% 0.22/0.51      (![X1, X0] : ((~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u54,negated_conjecture,
% 0.22/0.51      m1_pre_topc(sK1,sK0)).
% 0.22/0.51  
% 0.22/0.51  % (32334)# SZS output end Saturation.
% 0.22/0.51  % (32334)------------------------------
% 0.22/0.51  % (32334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (32334)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (32334)Memory used [KB]: 5373
% 0.22/0.51  % (32334)Time elapsed: 0.053 s
% 0.22/0.51  % (32334)------------------------------
% 0.22/0.51  % (32334)------------------------------
% 0.22/0.51  % (32333)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.51  % (32326)Success in time 0.143 s
%------------------------------------------------------------------------------
