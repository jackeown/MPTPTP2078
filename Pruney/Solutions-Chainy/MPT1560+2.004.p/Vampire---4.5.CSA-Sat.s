%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:06 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    0
%              Number of atoms          :   52 (  52 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u97,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k2_tarski(sK1,sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

tff(u96,negated_conjecture,
    ( k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) != k2_tarski(u1_orders_2(sK0),u1_orders_2(sK0))
    | k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) = k2_tarski(u1_orders_2(sK0),u1_orders_2(sK0)) )).

tff(u95,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sK3 = X0 ) )).

tff(u94,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) )).

tff(u93,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | v1_xboole_0(u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u92,axiom,(
    ! [X1,X0,X2] :
      ( ~ v1_xboole_0(u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2) ) )).

tff(u91,axiom,(
    v1_xboole_0(sK3) )).

tff(u90,axiom,(
    ! [X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) )).

tff(u89,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u88,axiom,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) )).

tff(u87,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u86,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) )).

tff(u85,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) )).

tff(u84,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u83,axiom,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) )).

tff(u82,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))),u1_orders_2(X0)) = k2_tarski(u1_orders_2(X0),u1_orders_2(X0)) ) )).

tff(u81,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u80,axiom,(
    ! [X1,X0] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u79,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u78,negated_conjecture,(
    v3_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:20:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (23272)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (23280)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.48  % (23280)# SZS output start Saturation.
% 0.22/0.48  tff(u97,negated_conjecture,
% 0.22/0.48      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)))).
% 0.22/0.48  
% 0.22/0.48  tff(u96,negated_conjecture,
% 0.22/0.48      ((~(k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) = k2_tarski(u1_orders_2(sK0),u1_orders_2(sK0)))) | (k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) = k2_tarski(u1_orders_2(sK0),u1_orders_2(sK0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u95,axiom,
% 0.22/0.48      (![X0] : ((~v1_xboole_0(X0) | (sK3 = X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u94,axiom,
% 0.22/0.48      (![X1, X0] : ((~v1_xboole_0(X0) | (X0 = X1) | ~v1_xboole_0(X1))))).
% 0.22/0.48  
% 0.22/0.48  tff(u93,axiom,
% 0.22/0.48      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | v1_xboole_0(u1_orders_2(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u92,axiom,
% 0.22/0.48      (![X1, X0, X2] : ((~v1_xboole_0(u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2))))).
% 0.22/0.48  
% 0.22/0.48  tff(u91,axiom,
% 0.22/0.48      v1_xboole_0(sK3)).
% 0.22/0.48  
% 0.22/0.48  tff(u90,axiom,
% 0.22/0.48      (![X0, X2] : ((~r2_hidden(X2,X0) | ~v1_xboole_0(X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u89,axiom,
% 0.22/0.48      (![X1, X0, X2] : ((~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u88,axiom,
% 0.22/0.48      (![X0] : ((r2_hidden(sK2(X0),X0) | v1_xboole_0(X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u87,axiom,
% 0.22/0.48      (![X1, X0, X2] : ((r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u86,axiom,
% 0.22/0.48      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_xboole_0(X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u85,axiom,
% 0.22/0.48      (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k2_tarski(X1,X1)) | v1_xboole_0(X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u84,negated_conjecture,
% 0.22/0.48      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.48  
% 0.22/0.48  tff(u83,axiom,
% 0.22/0.48      (![X0] : ((m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u82,axiom,
% 0.22/0.48      (![X0] : ((~l1_orders_2(X0) | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | (k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))),u1_orders_2(X0)) = k2_tarski(u1_orders_2(X0),u1_orders_2(X0))))))).
% 0.22/0.48  
% 0.22/0.48  tff(u81,negated_conjecture,
% 0.22/0.48      l1_orders_2(sK0)).
% 0.22/0.48  
% 0.22/0.48  tff(u80,axiom,
% 0.22/0.48      (![X1, X0] : ((r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u79,negated_conjecture,
% 0.22/0.48      ~v2_struct_0(sK0)).
% 0.22/0.48  
% 0.22/0.48  tff(u78,negated_conjecture,
% 0.22/0.48      v3_orders_2(sK0)).
% 0.22/0.48  
% 0.22/0.48  % (23280)# SZS output end Saturation.
% 0.22/0.48  % (23280)------------------------------
% 0.22/0.48  % (23280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (23280)Termination reason: Satisfiable
% 0.22/0.48  
% 0.22/0.48  % (23280)Memory used [KB]: 6140
% 0.22/0.48  % (23280)Time elapsed: 0.046 s
% 0.22/0.48  % (23280)------------------------------
% 0.22/0.48  % (23280)------------------------------
% 0.22/0.48  % (23267)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (23281)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (23265)Success in time 0.113 s
%------------------------------------------------------------------------------
