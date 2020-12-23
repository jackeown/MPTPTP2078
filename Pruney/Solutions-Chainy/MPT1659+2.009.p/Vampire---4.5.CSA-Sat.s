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
% DateTime   : Thu Dec  3 13:17:13 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    0
%              Number of atoms          :   98 (  98 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u164,negated_conjecture,
    ( ~ ( sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) )
    | sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) )).

tff(u163,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) )).

tff(u162,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1)
    | sK1 = k1_yellow_0(sK0,k1_tarski(sK1)) )).

tff(u161,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1)
    | sK1 = k2_yellow_0(sK0,k1_tarski(sK1)) )).

tff(u160,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u159,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u158,negated_conjecture,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK1) )).

tff(u157,axiom,(
    ! [X1,X0] :
      ( v1_xboole_0(k1_tarski(X0))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(k1_zfmisc_1(X1)) ) )).

tff(u156,axiom,(
    ! [X5,X4] :
      ( v1_xboole_0(k1_zfmisc_1(X4))
      | k6_domain_1(k1_zfmisc_1(X4),k1_tarski(X5)) = k1_tarski(k1_tarski(X5))
      | ~ r2_hidden(X5,X4) ) )).

tff(u155,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) )).

tff(u154,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) )).

tff(u153,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) )).

tff(u152,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) )).

tff(u151,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u150,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u149,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) )).

tff(u148,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) )).

tff(u147,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) )).

tff(u146,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
      | ~ v3_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) )).

tff(u145,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
      | ~ v3_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) )).

tff(u144,axiom,(
    ! [X1,X0] :
      ( r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) )).

tff(u143,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u142,axiom,(
    ! [X3,X2] :
      ( v2_struct_0(X2)
      | ~ v5_orders_2(X2)
      | ~ l1_orders_2(X2)
      | ~ v3_orders_2(X2)
      | k2_yellow_0(X2,k6_domain_1(u1_struct_0(X2),X3)) = X3
      | ~ v1_xboole_0(X3)
      | ~ v1_xboole_0(u1_struct_0(X2)) ) )).

tff(u141,axiom,(
    ! [X3,X2] :
      ( v2_struct_0(X2)
      | ~ v5_orders_2(X2)
      | ~ l1_orders_2(X2)
      | ~ v3_orders_2(X2)
      | k1_yellow_0(X2,k6_domain_1(u1_struct_0(X2),X3)) = X3
      | ~ v1_xboole_0(X3)
      | ~ v1_xboole_0(u1_struct_0(X2)) ) )).

tff(u140,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u139,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u138,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u137,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u136,negated_conjecture,
    ( ~ ~ r2_yellow_0(sK0,k6_waybel_0(sK0,sK1))
    | ~ r2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) )).

tff(u135,axiom,(
    ! [X1,X0] :
      ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ v3_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) )).

tff(u134,negated_conjecture,
    ( ~ r2_yellow_0(sK0,k1_tarski(sK1))
    | r2_yellow_0(sK0,k1_tarski(sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (25636)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.47  % (25644)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.47  % (25636)# SZS output start Saturation.
% 0.20/0.47  tff(u164,negated_conjecture,
% 0.20/0.47      ((~(sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)))) | (sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u163,negated_conjecture,
% 0.20/0.47      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)))).
% 0.20/0.47  
% 0.20/0.47  tff(u162,negated_conjecture,
% 0.20/0.47      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1))) | (sK1 = k1_yellow_0(sK0,k1_tarski(sK1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u161,negated_conjecture,
% 0.20/0.47      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1))) | (sK1 = k2_yellow_0(sK0,k1_tarski(sK1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u160,axiom,
% 0.20/0.47      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u159,negated_conjecture,
% 0.20/0.47      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.20/0.47  
% 0.20/0.47  tff(u158,negated_conjecture,
% 0.20/0.47      ((~v1_xboole_0(sK1)) | v1_xboole_0(sK1))).
% 0.20/0.47  
% 0.20/0.47  tff(u157,axiom,
% 0.20/0.47      (![X1, X0] : ((v1_xboole_0(k1_tarski(X0)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(k1_zfmisc_1(X1)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u156,axiom,
% 0.20/0.47      (![X5, X4] : ((v1_xboole_0(k1_zfmisc_1(X4)) | (k6_domain_1(k1_zfmisc_1(X4),k1_tarski(X5)) = k1_tarski(k1_tarski(X5))) | ~r2_hidden(X5,X4))))).
% 0.20/0.47  
% 0.20/0.47  tff(u155,axiom,
% 0.20/0.47      (![X1, X0] : ((~m1_subset_1(X1,X0) | v1_xboole_0(X0) | (k6_domain_1(X0,X1) = k1_tarski(X1)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u154,axiom,
% 0.20/0.47      (![X1, X0] : ((~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u153,axiom,
% 0.20/0.47      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | (k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u152,axiom,
% 0.20/0.47      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | (k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u151,negated_conjecture,
% 0.20/0.47      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.20/0.47  
% 0.20/0.47  tff(u150,axiom,
% 0.20/0.47      (![X1, X0] : ((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u149,axiom,
% 0.20/0.47      (![X1, X0] : ((m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u148,axiom,
% 0.20/0.47      (![X1, X0] : ((m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u147,axiom,
% 0.20/0.47      (![X1, X0] : ((~r2_hidden(X1,X0) | (k6_domain_1(X0,X1) = k1_tarski(X1)) | v1_xboole_0(X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u146,axiom,
% 0.20/0.47      (![X1, X0] : ((~r2_hidden(X1,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | (k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~v3_orders_2(X0) | v1_xboole_0(u1_struct_0(X0)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u145,axiom,
% 0.20/0.47      (![X1, X0] : ((~r2_hidden(X1,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | (k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~v3_orders_2(X0) | v1_xboole_0(u1_struct_0(X0)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u144,axiom,
% 0.20/0.47      (![X1, X0] : ((r2_hidden(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u143,negated_conjecture,
% 0.20/0.47      ~v2_struct_0(sK0)).
% 0.20/0.47  
% 0.20/0.47  tff(u142,axiom,
% 0.20/0.47      (![X3, X2] : ((v2_struct_0(X2) | ~v5_orders_2(X2) | ~l1_orders_2(X2) | ~v3_orders_2(X2) | (k2_yellow_0(X2,k6_domain_1(u1_struct_0(X2),X3)) = X3) | ~v1_xboole_0(X3) | ~v1_xboole_0(u1_struct_0(X2)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u141,axiom,
% 0.20/0.47      (![X3, X2] : ((v2_struct_0(X2) | ~v5_orders_2(X2) | ~l1_orders_2(X2) | ~v3_orders_2(X2) | (k1_yellow_0(X2,k6_domain_1(u1_struct_0(X2),X3)) = X3) | ~v1_xboole_0(X3) | ~v1_xboole_0(u1_struct_0(X2)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u140,axiom,
% 0.20/0.47      (![X0] : ((l1_struct_0(X0) | ~l1_orders_2(X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u139,negated_conjecture,
% 0.20/0.47      l1_orders_2(sK0)).
% 0.20/0.47  
% 0.20/0.47  tff(u138,negated_conjecture,
% 0.20/0.47      v3_orders_2(sK0)).
% 0.20/0.47  
% 0.20/0.47  tff(u137,negated_conjecture,
% 0.20/0.47      v5_orders_2(sK0)).
% 0.20/0.47  
% 0.20/0.47  tff(u136,negated_conjecture,
% 0.20/0.47      ((~~r2_yellow_0(sK0,k6_waybel_0(sK0,sK1))) | ~r2_yellow_0(sK0,k6_waybel_0(sK0,sK1)))).
% 0.20/0.47  
% 0.20/0.47  tff(u135,axiom,
% 0.20/0.47      (![X1, X0] : ((r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~v3_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u134,negated_conjecture,
% 0.20/0.47      ((~r2_yellow_0(sK0,k1_tarski(sK1))) | r2_yellow_0(sK0,k1_tarski(sK1)))).
% 0.20/0.47  
% 0.20/0.47  % (25636)# SZS output end Saturation.
% 0.20/0.47  % (25636)------------------------------
% 0.20/0.47  % (25636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (25636)Termination reason: Satisfiable
% 0.20/0.47  
% 0.20/0.47  % (25636)Memory used [KB]: 10618
% 0.20/0.47  % (25636)Time elapsed: 0.053 s
% 0.20/0.47  % (25636)------------------------------
% 0.20/0.47  % (25636)------------------------------
% 0.20/0.48  % (25623)Success in time 0.121 s
%------------------------------------------------------------------------------
