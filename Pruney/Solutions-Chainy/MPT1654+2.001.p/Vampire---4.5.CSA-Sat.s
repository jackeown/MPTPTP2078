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
% DateTime   : Thu Dec  3 13:17:07 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    0
%              Number of atoms          :   35 (  35 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u54,negated_conjecture,
    ( ~ ( sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) )
    | sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) )).

tff(u53,negated_conjecture,(
    sK1 = k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

tff(u52,negated_conjecture,(
    sK1 = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

tff(u51,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) )).

tff(u50,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) )).

tff(u49,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) )).

tff(u48,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u47,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u46,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u45,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u44,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u43,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u42,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | ~ r1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) )).

tff(u41,axiom,(
    ! [X1,X0] :
      ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ v3_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:22:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (19019)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.52  % (19032)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.52  % (19024)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.52  % (19024)# SZS output start Saturation.
% 0.22/0.52  tff(u54,negated_conjecture,
% 0.22/0.52      ((~(sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)))) | (sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u53,negated_conjecture,
% 0.22/0.52      (sK1 = k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))).
% 0.22/0.52  
% 0.22/0.52  tff(u52,negated_conjecture,
% 0.22/0.52      (sK1 = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))).
% 0.22/0.52  
% 0.22/0.52  tff(u51,axiom,
% 0.22/0.52      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u50,axiom,
% 0.22/0.52      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | (k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u49,axiom,
% 0.22/0.52      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | (k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u48,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.52  
% 0.22/0.52  tff(u47,axiom,
% 0.22/0.52      (![X1, X0] : ((m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u46,negated_conjecture,
% 0.22/0.52      ~v2_struct_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u45,negated_conjecture,
% 0.22/0.52      v3_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u44,negated_conjecture,
% 0.22/0.52      v5_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u43,negated_conjecture,
% 0.22/0.52      l1_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u42,negated_conjecture,
% 0.22/0.52      ((~~r1_yellow_0(sK0,k5_waybel_0(sK0,sK1))) | ~r1_yellow_0(sK0,k5_waybel_0(sK0,sK1)))).
% 0.22/0.52  
% 0.22/0.52  tff(u41,axiom,
% 0.22/0.52      (![X1, X0] : ((r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~v3_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  % (19024)# SZS output end Saturation.
% 0.22/0.52  % (19024)------------------------------
% 0.22/0.52  % (19024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19024)Termination reason: Satisfiable
% 0.22/0.52  
% 0.22/0.52  % (19024)Memory used [KB]: 10618
% 0.22/0.52  % (19024)Time elapsed: 0.077 s
% 0.22/0.52  % (19024)------------------------------
% 0.22/0.52  % (19024)------------------------------
% 0.22/0.53  % (19004)Success in time 0.162 s
%------------------------------------------------------------------------------
