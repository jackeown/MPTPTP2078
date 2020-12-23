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
% DateTime   : Thu Dec  3 13:16:08 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   32 (  32 expanded)
%              Depth                    :    0
%              Number of atoms          :   98 (  98 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u120,negated_conjecture,
    ( ~ ( sK1 != k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    | k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1)
    | sK1 != k1_yellow_0(sK0,k1_tarski(sK1)) )).

tff(u119,negated_conjecture,
    ( ~ ( sK1 != k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    | k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1)
    | sK1 != k2_yellow_0(sK0,k1_tarski(sK1)) )).

tff(u118,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) )).

tff(u117,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(sK2(X0))
      | v1_xboole_0(X0) ) )).

tff(u116,negated_conjecture,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u115,negated_conjecture,(
    ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u114,axiom,(
    ! [X0] :
      ( v1_xboole_0(k1_zfmisc_1(X0))
      | k6_domain_1(k1_zfmisc_1(X0),sK2(X0)) = k1_tarski(sK2(X0))
      | v1_xboole_0(X0) ) )).

tff(u113,axiom,(
    ! [X1] :
      ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
      | k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))),u1_orders_2(X1)) = k1_tarski(u1_orders_2(X1))
      | ~ l1_orders_2(X1) ) )).

tff(u112,axiom,(
    ! [X1,X0] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) )).

tff(u111,axiom,(
    ! [X0] :
      ( v1_xboole_0(u1_orders_2(X0))
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u110,axiom,(
    ! [X1,X0] :
      ( v1_xboole_0(sK2(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_zfmisc_1(X0,X1)) ) )).

tff(u109,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) )).

tff(u108,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) )).

tff(u107,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) )).

tff(u106,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u105,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X1)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u104,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) )).

tff(u103,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u102,axiom,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) )).

tff(u101,axiom,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) )).

tff(u100,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) )).

tff(u99,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X0,u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_xboole_0(u1_struct_0(X1)) ) )).

tff(u98,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))
      | ~ r2_hidden(X2,u1_orders_2(X1))
      | ~ l1_orders_2(X1) ) )).

tff(u97,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) )).

tff(u96,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2) ) )).

tff(u95,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u94,axiom,(
    ! [X1,X0,X2] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u93,axiom,(
    ! [X3,X5,X4,X6] :
      ( ~ m1_subset_1(u1_orders_2(X4),k1_zfmisc_1(X6))
      | ~ r1_orders_2(X4,X3,X5)
      | ~ l1_orders_2(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ v1_xboole_0(X6) ) )).

tff(u92,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u91,axiom,(
    ! [X1,X0] :
      ( r1_orders_2(X0,X1,X1)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) )).

tff(u90,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u89,negated_conjecture,(
    v3_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:06:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (26663)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.48  % (26671)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.49  % (26666)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.49  % (26671)Refutation not found, incomplete strategy% (26671)------------------------------
% 0.21/0.49  % (26671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (26671)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (26671)Memory used [KB]: 10490
% 0.21/0.49  % (26671)Time elapsed: 0.074 s
% 0.21/0.49  % (26671)------------------------------
% 0.21/0.49  % (26671)------------------------------
% 0.21/0.49  % (26673)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (26665)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (26673)# SZS output start Saturation.
% 0.21/0.49  tff(u120,negated_conjecture,
% 0.21/0.49      ((~(sK1 != k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))) | (~(k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1))) | (sK1 != k1_yellow_0(sK0,k1_tarski(sK1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u119,negated_conjecture,
% 0.21/0.49      ((~(sK1 != k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))) | (~(k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1))) | (sK1 != k2_yellow_0(sK0,k1_tarski(sK1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u118,negated_conjecture,
% 0.21/0.49      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)))).
% 0.21/0.49  
% 0.21/0.49  tff(u117,axiom,
% 0.21/0.49      (![X0] : ((~v1_xboole_0(sK2(X0)) | v1_xboole_0(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u116,negated_conjecture,
% 0.21/0.49      ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.49  
% 0.21/0.49  tff(u115,negated_conjecture,
% 0.21/0.49      ~v1_xboole_0(u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  tff(u114,axiom,
% 0.21/0.49      (![X0] : ((v1_xboole_0(k1_zfmisc_1(X0)) | (k6_domain_1(k1_zfmisc_1(X0),sK2(X0)) = k1_tarski(sK2(X0))) | v1_xboole_0(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u113,axiom,
% 0.21/0.49      (![X1] : ((v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) | (k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))),u1_orders_2(X1)) = k1_tarski(u1_orders_2(X1))) | ~l1_orders_2(X1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u112,axiom,
% 0.21/0.49      (![X1, X0] : ((v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u111,axiom,
% 0.21/0.49      (![X0] : ((v1_xboole_0(u1_orders_2(X0)) | ~v1_xboole_0(u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u110,axiom,
% 0.21/0.49      (![X1, X0] : ((v1_xboole_0(sK2(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u109,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_xboole_0(X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u108,axiom,
% 0.21/0.49      (![X1, X0] : ((~m1_subset_1(X1,X0) | v1_xboole_0(X0) | (k6_domain_1(X0,X1) = k1_tarski(X1)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u107,axiom,
% 0.21/0.49      (![X1, X0] : ((~v1_xboole_0(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u106,axiom,
% 0.21/0.49      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_xboole_0(u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u105,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_xboole_0(X1) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u104,negated_conjecture,
% 0.21/0.49      (![X0] : ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(X0)) | ~v1_xboole_0(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u103,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  tff(u102,axiom,
% 0.21/0.49      (![X0] : ((m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) | v1_xboole_0(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u101,axiom,
% 0.21/0.49      (![X0] : ((m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u100,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u99,axiom,
% 0.21/0.49      (![X1, X0] : ((~r2_hidden(X0,u1_orders_2(X1)) | ~l1_orders_2(X1) | ~v1_xboole_0(u1_struct_0(X1)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u98,axiom,
% 0.21/0.49      (![X1, X2] : ((~v1_xboole_0(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))) | ~r2_hidden(X2,u1_orders_2(X1)) | ~l1_orders_2(X1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u97,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u96,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u95,negated_conjecture,
% 0.21/0.49      l1_orders_2(sK0)).
% 0.21/0.49  
% 0.21/0.49  tff(u94,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~v1_xboole_0(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u93,axiom,
% 0.21/0.49      (![X3, X5, X4, X6] : ((~m1_subset_1(u1_orders_2(X4),k1_zfmisc_1(X6)) | ~r1_orders_2(X4,X3,X5) | ~l1_orders_2(X4) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~m1_subset_1(X3,u1_struct_0(X4)) | ~v1_xboole_0(X6))))).
% 0.21/0.49  
% 0.21/0.49  tff(u92,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~v1_xboole_0(u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u91,axiom,
% 0.21/0.49      (![X1, X0] : ((r1_orders_2(X0,X1,X1) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u90,negated_conjecture,
% 0.21/0.49      ~v2_struct_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  tff(u89,negated_conjecture,
% 0.21/0.49      v3_orders_2(sK0)).
% 0.21/0.49  
% 0.21/0.49  % (26673)# SZS output end Saturation.
% 0.21/0.49  % (26673)------------------------------
% 0.21/0.49  % (26673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (26673)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (26673)Memory used [KB]: 10618
% 0.21/0.49  % (26673)Time elapsed: 0.077 s
% 0.21/0.49  % (26673)------------------------------
% 0.21/0.49  % (26673)------------------------------
% 0.21/0.49  % (26672)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.49  % (26685)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.49  % (26662)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.49  % (26685)Refutation not found, incomplete strategy% (26685)------------------------------
% 0.21/0.49  % (26685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (26685)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (26685)Memory used [KB]: 10618
% 0.21/0.49  % (26685)Time elapsed: 0.051 s
% 0.21/0.49  % (26685)------------------------------
% 0.21/0.49  % (26685)------------------------------
% 0.21/0.49  % (26667)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.50  % (26661)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (26680)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.50  % (26674)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.50  % (26668)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (26668)Refutation not found, incomplete strategy% (26668)------------------------------
% 0.21/0.50  % (26668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26668)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26668)Memory used [KB]: 6012
% 0.21/0.50  % (26668)Time elapsed: 0.056 s
% 0.21/0.50  % (26668)------------------------------
% 0.21/0.50  % (26668)------------------------------
% 0.21/0.50  % (26681)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (26681)Refutation not found, incomplete strategy% (26681)------------------------------
% 0.21/0.50  % (26681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26681)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26681)Memory used [KB]: 6140
% 0.21/0.50  % (26681)Time elapsed: 0.102 s
% 0.21/0.50  % (26681)------------------------------
% 0.21/0.50  % (26681)------------------------------
% 0.21/0.50  % (26684)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.50  % (26683)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.50  % (26676)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.50  % (26678)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.51  % (26664)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (26664)Refutation not found, incomplete strategy% (26664)------------------------------
% 0.21/0.51  % (26664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26664)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26664)Memory used [KB]: 10618
% 0.21/0.51  % (26664)Time elapsed: 0.096 s
% 0.21/0.51  % (26664)------------------------------
% 0.21/0.51  % (26664)------------------------------
% 0.21/0.51  % (26682)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.51  % (26682)Refutation not found, incomplete strategy% (26682)------------------------------
% 0.21/0.51  % (26682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26682)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26682)Memory used [KB]: 6140
% 0.21/0.51  % (26682)Time elapsed: 0.103 s
% 0.21/0.51  % (26682)------------------------------
% 0.21/0.51  % (26682)------------------------------
% 0.21/0.51  % (26658)Success in time 0.149 s
%------------------------------------------------------------------------------
