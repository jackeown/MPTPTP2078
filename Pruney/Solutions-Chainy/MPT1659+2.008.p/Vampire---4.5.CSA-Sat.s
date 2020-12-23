%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:13 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
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

tff(u154,axiom,(
    ! [X1,X0] :
      ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u153,negated_conjecture,
    ( ~ r1_yellow_0(sK0,k1_tarski(sK1))
    | r1_yellow_0(sK0,k1_tarski(sK1)) )).

tff(u152,negated_conjecture,
    ( ~ ~ r2_yellow_0(sK0,k6_waybel_0(sK0,sK1))
    | ~ r2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) )).

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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:04:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (29797)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.46  % (29788)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.46  % (29789)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (29798)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (29790)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (29784)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (29785)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (29788)Refutation not found, incomplete strategy% (29788)------------------------------
% 0.22/0.48  % (29788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (29788)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (29788)Memory used [KB]: 6140
% 0.22/0.48  % (29788)Time elapsed: 0.055 s
% 0.22/0.48  % (29788)------------------------------
% 0.22/0.48  % (29788)------------------------------
% 0.22/0.49  % (29792)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (29787)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (29800)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (29787)Refutation not found, incomplete strategy% (29787)------------------------------
% 0.22/0.49  % (29787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (29787)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (29787)Memory used [KB]: 1663
% 0.22/0.49  % (29787)Time elapsed: 0.085 s
% 0.22/0.49  % (29787)------------------------------
% 0.22/0.49  % (29787)------------------------------
% 0.22/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.49  % (29800)# SZS output start Saturation.
% 0.22/0.49  tff(u183,axiom,
% 0.22/0.49      (![X0] : ((k2_tarski(X0,X0) = k1_tarski(X0))))).
% 0.22/0.49  
% 0.22/0.49  tff(u182,negated_conjecture,
% 0.22/0.49      ((~~v1_xboole_0(u1_struct_0(sK0))) | (k1_tarski(sK1) = k6_domain_1(u1_struct_0(sK0),sK1)))).
% 0.22/0.49  
% 0.22/0.49  tff(u181,axiom,
% 0.22/0.49      (![X1, X0] : ((k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u180,negated_conjecture,
% 0.22/0.49      ((~~v1_xboole_0(u1_struct_0(sK0))) | (~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0))))) | (sK1 = k1_yellow_0(sK0,k1_tarski(sK1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u179,negated_conjecture,
% 0.22/0.49      ((~~v1_xboole_0(u1_struct_0(sK0))) | (~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0))))) | (sK1 = k2_yellow_0(sK0,k1_tarski(sK1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u178,negated_conjecture,
% 0.22/0.49      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.22/0.49  
% 0.22/0.49  tff(u177,axiom,
% 0.22/0.49      (![X1, X0] : ((v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k1_tarski(X1)))))).
% 0.22/0.49  
% 0.22/0.49  tff(u176,axiom,
% 0.22/0.49      (![X0, X2] : ((~r2_hidden(X2,X0) | ~v1_xboole_0(X0))))).
% 0.22/0.49  
% 0.22/0.49  tff(u175,axiom,
% 0.22/0.49      (![X0] : ((r2_hidden(sK2(X0),X0) | v1_xboole_0(X0))))).
% 0.22/0.49  
% 0.22/0.49  tff(u174,axiom,
% 0.22/0.49      (![X1, X0] : ((r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u173,axiom,
% 0.22/0.49      (![X1, X0] : ((r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u172,axiom,
% 0.22/0.49      (![X1, X0] : ((~r1_tarski(k1_tarski(X0),X1) | ~v1_xboole_0(X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u171,axiom,
% 0.22/0.49      (![X1, X0] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u170,axiom,
% 0.22/0.49      (![X1, X0] : ((r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))))).
% 0.22/0.49  
% 0.22/0.49  tff(u169,axiom,
% 0.22/0.49      (![X1, X0] : ((~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~v1_xboole_0(X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u168,negated_conjecture,
% 0.22/0.49      ((~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0))))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0)))))).
% 0.22/0.49  
% 0.22/0.49  tff(u167,negated_conjecture,
% 0.22/0.49      ((~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0))))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0)))))).
% 0.22/0.49  
% 0.22/0.49  tff(u166,negated_conjecture,
% 0.22/0.49      ((~~v1_xboole_0(u1_struct_0(sK0))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),X0))))))).
% 0.22/0.49  
% 0.22/0.49  tff(u165,axiom,
% 0.22/0.49      (![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u164,negated_conjecture,
% 0.22/0.49      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.49  
% 0.22/0.49  tff(u163,negated_conjecture,
% 0.22/0.49      ~v2_struct_0(sK0)).
% 0.22/0.49  
% 0.22/0.49  tff(u162,axiom,
% 0.22/0.49      (![X1, X0] : ((v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | (k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u161,axiom,
% 0.22/0.49      (![X1, X0] : ((v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | (k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u160,axiom,
% 0.22/0.49      (![X0] : ((v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)))))).
% 0.22/0.49  
% 0.22/0.49  tff(u159,axiom,
% 0.22/0.49      (![X0] : ((l1_struct_0(X0) | ~l1_orders_2(X0))))).
% 0.22/0.49  
% 0.22/0.49  tff(u158,negated_conjecture,
% 0.22/0.49      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.22/0.49  
% 0.22/0.49  tff(u157,negated_conjecture,
% 0.22/0.49      l1_orders_2(sK0)).
% 0.22/0.49  
% 0.22/0.49  tff(u156,negated_conjecture,
% 0.22/0.49      v3_orders_2(sK0)).
% 0.22/0.49  
% 0.22/0.49  tff(u155,negated_conjecture,
% 0.22/0.49      v5_orders_2(sK0)).
% 0.22/0.49  
% 0.22/0.49  tff(u154,axiom,
% 0.22/0.49      (![X1, X0] : ((r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.49  
% 0.22/0.49  tff(u153,negated_conjecture,
% 0.22/0.49      ((~r1_yellow_0(sK0,k1_tarski(sK1))) | r1_yellow_0(sK0,k1_tarski(sK1)))).
% 0.22/0.49  
% 0.22/0.49  tff(u152,negated_conjecture,
% 0.22/0.49      ((~~r2_yellow_0(sK0,k6_waybel_0(sK0,sK1))) | ~r2_yellow_0(sK0,k6_waybel_0(sK0,sK1)))).
% 0.22/0.49  
% 0.22/0.49  tff(u151,axiom,
% 0.22/0.49      (![X1, X0] : ((r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.49  
% 0.22/0.49  tff(u150,negated_conjecture,
% 0.22/0.49      ((~r2_yellow_0(sK0,k1_tarski(sK1))) | r2_yellow_0(sK0,k1_tarski(sK1)))).
% 0.22/0.49  
% 0.22/0.49  tff(u149,negated_conjecture,
% 0.22/0.49      v4_orders_2(sK0)).
% 0.22/0.49  
% 0.22/0.49  % (29800)# SZS output end Saturation.
% 0.22/0.49  % (29800)------------------------------
% 0.22/0.49  % (29800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (29800)Termination reason: Satisfiable
% 0.22/0.49  
% 0.22/0.49  % (29800)Memory used [KB]: 6140
% 0.22/0.49  % (29800)Time elapsed: 0.082 s
% 0.22/0.49  % (29800)------------------------------
% 0.22/0.49  % (29800)------------------------------
% 0.22/0.49  % (29799)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (29783)Success in time 0.134 s
%------------------------------------------------------------------------------
