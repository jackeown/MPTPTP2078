%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:08 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   35 (  35 expanded)
%              Depth                    :    0
%              Number of atoms          :   90 (  90 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u183,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) )).

tff(u182,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | k1_tarski(sK1) = k6_domain_1(u1_struct_0(sK0),sK1) )).

tff(u181,axiom,(
    ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) )).

tff(u180,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ ! [X0] :
          ( ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 )
    | sK1 = k1_yellow_0(sK0,k1_tarski(sK1)) )).

tff(u179,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ ! [X0] :
          ( ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 )
    | sK1 = k2_yellow_0(sK0,k1_tarski(sK1)) )).

tff(u178,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u177,axiom,(
    ! [X1,X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) )).

tff(u176,axiom,(
    ! [X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) )).

tff(u175,axiom,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) )).

tff(u174,axiom,(
    ! [X1,X0] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) )).

tff(u173,axiom,(
    ! [X1,X0] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) )).

tff(u172,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | ~ v1_xboole_0(X1) ) )).

tff(u171,axiom,(
    ! [X1,X0] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) )).

tff(u170,axiom,(
    ! [X1,X0] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) )).

tff(u169,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X1) ) )).

tff(u168,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 )
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 ) )).

tff(u167,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 )
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 ) )).

tff(u166,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),X0) ) )).

tff(u165,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) )).

tff(u164,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u163,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u162,axiom,(
    ! [X1,X0] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) )).

tff(u161,axiom,(
    ! [X1,X0] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) )).

tff(u160,axiom,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) )).

tff(u159,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u158,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

tff(u157,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u156,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u155,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u154,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | ~ r1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) )).

tff(u153,axiom,(
    ! [X1,X0] :
      ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u152,negated_conjecture,
    ( ~ r1_yellow_0(sK0,k1_tarski(sK1))
    | r1_yellow_0(sK0,k1_tarski(sK1)) )).

tff(u151,axiom,(
    ! [X1,X0] :
      ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u150,negated_conjecture,
    ( ~ r2_yellow_0(sK0,k1_tarski(sK1))
    | r2_yellow_0(sK0,k1_tarski(sK1)) )).

tff(u149,negated_conjecture,(
    v4_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:25:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.44  % (4311)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.45  % (4307)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.45  % (4307)Refutation not found, incomplete strategy% (4307)------------------------------
% 0.19/0.45  % (4307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (4307)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.45  
% 0.19/0.45  % (4307)Memory used [KB]: 1663
% 0.19/0.45  % (4307)Time elapsed: 0.071 s
% 0.19/0.45  % (4307)------------------------------
% 0.19/0.45  % (4307)------------------------------
% 0.19/0.45  % (4308)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.45  % (4306)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.45  % (4308)Refutation not found, incomplete strategy% (4308)------------------------------
% 0.19/0.45  % (4308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (4308)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.45  
% 0.19/0.45  % (4308)Memory used [KB]: 6140
% 0.19/0.45  % (4308)Time elapsed: 0.054 s
% 0.19/0.45  % (4308)------------------------------
% 0.19/0.45  % (4308)------------------------------
% 0.19/0.45  % (4313)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.46  % (4321)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.46  % (4317)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.46  % (4318)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.19/0.46  % (4321)# SZS output start Saturation.
% 0.19/0.46  tff(u183,axiom,
% 0.19/0.46      (![X0] : ((k2_tarski(X0,X0) = k1_tarski(X0))))).
% 0.19/0.46  
% 0.19/0.46  tff(u182,negated_conjecture,
% 0.19/0.46      ((~~v1_xboole_0(u1_struct_0(sK0))) | (k1_tarski(sK1) = k6_domain_1(u1_struct_0(sK0),sK1)))).
% 0.19/0.46  
% 0.19/0.46  tff(u181,axiom,
% 0.19/0.46      (![X1, X0] : ((k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1))))).
% 0.19/0.46  
% 0.19/0.46  tff(u180,negated_conjecture,
% 0.19/0.46      ((~~v1_xboole_0(u1_struct_0(sK0))) | (~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0))))) | (sK1 = k1_yellow_0(sK0,k1_tarski(sK1))))).
% 0.19/0.46  
% 0.19/0.46  tff(u179,negated_conjecture,
% 0.19/0.46      ((~~v1_xboole_0(u1_struct_0(sK0))) | (~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0))))) | (sK1 = k2_yellow_0(sK0,k1_tarski(sK1))))).
% 0.19/0.46  
% 0.19/0.46  tff(u178,negated_conjecture,
% 0.19/0.46      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.19/0.46  
% 0.19/0.46  tff(u177,axiom,
% 0.19/0.46      (![X1, X0] : ((v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k1_tarski(X1)))))).
% 0.19/0.46  
% 0.19/0.46  tff(u176,axiom,
% 0.19/0.46      (![X0, X2] : ((~r2_hidden(X2,X0) | ~v1_xboole_0(X0))))).
% 0.19/0.46  
% 0.19/0.46  tff(u175,axiom,
% 0.19/0.46      (![X0] : ((r2_hidden(sK2(X0),X0) | v1_xboole_0(X0))))).
% 0.19/0.46  
% 0.19/0.46  tff(u174,axiom,
% 0.19/0.46      (![X1, X0] : ((r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))))).
% 0.19/0.46  
% 0.19/0.46  tff(u173,axiom,
% 0.19/0.46      (![X1, X0] : ((r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1))))).
% 0.19/0.46  
% 0.19/0.46  tff(u172,axiom,
% 0.19/0.46      (![X1, X0] : ((~r1_tarski(k1_tarski(X0),X1) | ~v1_xboole_0(X1))))).
% 0.19/0.46  
% 0.19/0.46  tff(u171,axiom,
% 0.19/0.46      (![X1, X0] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))))).
% 0.19/0.46  
% 0.19/0.46  tff(u170,axiom,
% 0.19/0.46      (![X1, X0] : ((r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))))).
% 0.19/0.46  
% 0.19/0.46  tff(u169,axiom,
% 0.19/0.46      (![X1, X0] : ((~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~v1_xboole_0(X1))))).
% 0.19/0.46  
% 0.19/0.46  tff(u168,negated_conjecture,
% 0.19/0.46      ((~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0))))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0)))))).
% 0.19/0.46  
% 0.19/0.46  tff(u167,negated_conjecture,
% 0.19/0.46      ((~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0))))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0)))))).
% 0.19/0.46  
% 0.19/0.46  tff(u166,negated_conjecture,
% 0.19/0.46      ((~~v1_xboole_0(u1_struct_0(sK0))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),X0))))))).
% 0.19/0.46  
% 0.19/0.46  tff(u165,axiom,
% 0.19/0.46      (![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))))).
% 0.19/0.46  
% 0.19/0.46  tff(u164,negated_conjecture,
% 0.19/0.46      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.19/0.46  
% 0.19/0.46  tff(u163,negated_conjecture,
% 0.19/0.46      ~v2_struct_0(sK0)).
% 0.19/0.46  
% 0.19/0.46  tff(u162,axiom,
% 0.19/0.46      (![X1, X0] : ((v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | (k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1))))).
% 0.19/0.46  
% 0.19/0.46  tff(u161,axiom,
% 0.19/0.46      (![X1, X0] : ((v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | (k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1))))).
% 0.19/0.46  
% 0.19/0.46  tff(u160,axiom,
% 0.19/0.46      (![X0] : ((v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)))))).
% 0.19/0.46  
% 0.19/0.46  tff(u159,axiom,
% 0.19/0.46      (![X0] : ((l1_struct_0(X0) | ~l1_orders_2(X0))))).
% 0.19/0.46  
% 0.19/0.46  tff(u158,negated_conjecture,
% 0.19/0.46      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.19/0.46  
% 0.19/0.46  tff(u157,negated_conjecture,
% 0.19/0.46      l1_orders_2(sK0)).
% 0.19/0.46  
% 0.19/0.46  tff(u156,negated_conjecture,
% 0.19/0.46      v3_orders_2(sK0)).
% 0.19/0.46  
% 0.19/0.46  tff(u155,negated_conjecture,
% 0.19/0.46      v5_orders_2(sK0)).
% 0.19/0.46  
% 0.19/0.46  tff(u154,negated_conjecture,
% 0.19/0.46      ((~~r1_yellow_0(sK0,k5_waybel_0(sK0,sK1))) | ~r1_yellow_0(sK0,k5_waybel_0(sK0,sK1)))).
% 0.19/0.46  
% 0.19/0.46  tff(u153,axiom,
% 0.19/0.46      (![X1, X0] : ((r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.19/0.46  
% 0.19/0.46  tff(u152,negated_conjecture,
% 0.19/0.46      ((~r1_yellow_0(sK0,k1_tarski(sK1))) | r1_yellow_0(sK0,k1_tarski(sK1)))).
% 0.19/0.46  
% 0.19/0.46  tff(u151,axiom,
% 0.19/0.46      (![X1, X0] : ((r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.19/0.46  
% 0.19/0.46  tff(u150,negated_conjecture,
% 0.19/0.46      ((~r2_yellow_0(sK0,k1_tarski(sK1))) | r2_yellow_0(sK0,k1_tarski(sK1)))).
% 0.19/0.46  
% 0.19/0.46  tff(u149,negated_conjecture,
% 0.19/0.46      v4_orders_2(sK0)).
% 0.19/0.46  
% 0.19/0.46  % (4321)# SZS output end Saturation.
% 0.19/0.46  % (4321)------------------------------
% 0.19/0.46  % (4321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (4321)Termination reason: Satisfiable
% 0.19/0.46  
% 0.19/0.46  % (4321)Memory used [KB]: 6140
% 0.19/0.46  % (4321)Time elapsed: 0.063 s
% 0.19/0.46  % (4321)------------------------------
% 0.19/0.46  % (4321)------------------------------
% 0.19/0.46  % (4310)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.46  % (4303)Success in time 0.119 s
%------------------------------------------------------------------------------
