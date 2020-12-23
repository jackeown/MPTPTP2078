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
% DateTime   : Thu Dec  3 13:17:04 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    0
%              Number of atoms          :   46 (  46 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u87,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r1_tarski(X1,X2) ) )).

tff(u86,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK2(X0,X1,X2),X0)
      | r1_tarski(X1,X2) ) )).

tff(u85,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) )).

tff(u84,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u83,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2(u1_struct_0(sK0),sK1,X0),sK1)
      | r1_tarski(sK1,X0) ) )).

tff(u82,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK2(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0))
      | r1_tarski(sK1,X0) ) )).

tff(u81,negated_conjecture,
    ( ~ r1_tarski(sK1,sK1)
    | ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | r2_hidden(sK2(sK1,sK1,X1),sK1)
        | r1_tarski(sK1,X1) ) )).

tff(u80,negated_conjecture,
    ( ~ r1_tarski(sK1,sK1)
    | ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | m1_subset_1(sK2(sK1,sK1,X0),sK1)
        | r1_tarski(sK1,X0) ) )).

tff(u79,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u78,negated_conjecture,
    ( ~ r1_tarski(sK1,sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(sK1)) )).

tff(u77,negated_conjecture,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,u1_struct_0(sK0)) ) )).

tff(u76,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) )).

tff(u75,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) )).

tff(u74,negated_conjecture,
    ( ~ ~ r1_tarski(k4_waybel_0(sK0,sK1),sK1)
    | ~ r1_tarski(k4_waybel_0(sK0,sK1),sK1) )).

tff(u73,negated_conjecture,(
    r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u72,negated_conjecture,
    ( ~ r1_tarski(sK1,sK1)
    | r1_tarski(sK1,sK1) )).

tff(u71,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u70,negated_conjecture,
    ( ~ v13_waybel_0(sK1,sK0)
    | v13_waybel_0(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:15:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (27984)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.46  % (27982)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.47  % (27976)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.47  % (27974)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.48  % (27982)Refutation not found, incomplete strategy% (27982)------------------------------
% 0.21/0.48  % (27982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (27982)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (27982)Memory used [KB]: 9850
% 0.21/0.48  % (27982)Time elapsed: 0.053 s
% 0.21/0.48  % (27982)------------------------------
% 0.21/0.48  % (27982)------------------------------
% 0.21/0.49  % (27976)Refutation not found, incomplete strategy% (27976)------------------------------
% 0.21/0.49  % (27976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (27976)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (27976)Memory used [KB]: 9850
% 0.21/0.49  % (27976)Time elapsed: 0.060 s
% 0.21/0.49  % (27976)------------------------------
% 0.21/0.49  % (27976)------------------------------
% 0.21/0.49  % (27973)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (27973)Refutation not found, incomplete strategy% (27973)------------------------------
% 0.21/0.49  % (27973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (27973)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (27973)Memory used [KB]: 5373
% 0.21/0.49  % (27973)Time elapsed: 0.076 s
% 0.21/0.49  % (27973)------------------------------
% 0.21/0.49  % (27973)------------------------------
% 0.21/0.49  % (27988)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.50  % (27978)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.50  % (27978)Refutation not found, incomplete strategy% (27978)------------------------------
% 0.21/0.50  % (27978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (27978)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (27978)Memory used [KB]: 895
% 0.21/0.50  % (27978)Time elapsed: 0.082 s
% 0.21/0.50  % (27978)------------------------------
% 0.21/0.50  % (27978)------------------------------
% 0.21/0.50  % (27981)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (27977)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.51  % (27979)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.51  % (27983)WARNING: option uwaf not known.
% 0.21/0.51  % (27980)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.51  % (27990)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (27979)# SZS output start Saturation.
% 0.21/0.51  tff(u87,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK2(X0,X1,X2),X1) | r1_tarski(X1,X2))))).
% 0.21/0.51  
% 0.21/0.51  tff(u86,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK2(X0,X1,X2),X0) | r1_tarski(X1,X2))))).
% 0.21/0.51  
% 0.21/0.51  tff(u85,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u84,axiom,
% 0.21/0.51      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 0.21/0.51  
% 0.21/0.51  tff(u83,negated_conjecture,
% 0.21/0.51      (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2(u1_struct_0(sK0),sK1,X0),sK1) | r1_tarski(sK1,X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u82,negated_conjecture,
% 0.21/0.51      (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0)) | r1_tarski(sK1,X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u81,negated_conjecture,
% 0.21/0.51      ((~r1_tarski(sK1,sK1)) | (![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(sK1)) | r2_hidden(sK2(sK1,sK1,X1),sK1) | r1_tarski(sK1,X1)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u80,negated_conjecture,
% 0.21/0.51      ((~r1_tarski(sK1,sK1)) | (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(sK1)) | m1_subset_1(sK2(sK1,sK1,X0),sK1) | r1_tarski(sK1,X0)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u79,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  tff(u78,negated_conjecture,
% 0.21/0.51      ((~r1_tarski(sK1,sK1)) | m1_subset_1(sK1,k1_zfmisc_1(sK1)))).
% 0.21/0.51  
% 0.21/0.51  tff(u77,negated_conjecture,
% 0.21/0.51      (![X0] : ((~r2_hidden(X0,sK1) | r2_hidden(X0,u1_struct_0(sK0)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u76,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~r2_hidden(sK2(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2))))).
% 0.21/0.51  
% 0.21/0.51  tff(u75,axiom,
% 0.21/0.51      (![X1, X0] : ((~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u74,negated_conjecture,
% 0.21/0.51      ((~~r1_tarski(k4_waybel_0(sK0,sK1),sK1)) | ~r1_tarski(k4_waybel_0(sK0,sK1),sK1))).
% 0.21/0.51  
% 0.21/0.51  tff(u73,negated_conjecture,
% 0.21/0.51      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  tff(u72,negated_conjecture,
% 0.21/0.51      ((~r1_tarski(sK1,sK1)) | r1_tarski(sK1,sK1))).
% 0.21/0.51  
% 0.21/0.51  tff(u71,negated_conjecture,
% 0.21/0.51      l1_orders_2(sK0)).
% 0.21/0.51  
% 0.21/0.51  tff(u70,negated_conjecture,
% 0.21/0.51      ((~v13_waybel_0(sK1,sK0)) | v13_waybel_0(sK1,sK0))).
% 0.21/0.51  
% 0.21/0.51  % (27979)# SZS output end Saturation.
% 0.21/0.51  % (27979)------------------------------
% 0.21/0.51  % (27979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27979)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (27979)Memory used [KB]: 5373
% 0.21/0.51  % (27979)Time elapsed: 0.092 s
% 0.21/0.51  % (27979)------------------------------
% 0.21/0.51  % (27979)------------------------------
% 0.21/0.51  % (27972)Success in time 0.148 s
%------------------------------------------------------------------------------
