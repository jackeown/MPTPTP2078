%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:08 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    0
%              Number of atoms          :   85 (  85 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u240,negated_conjecture,
    ( ~ ( sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) )
    | sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) )).

tff(u239,negated_conjecture,
    ( ~ ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK1,sK1)) != k2_tarski(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)) )
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK1,sK1)) != k2_tarski(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)) )).

tff(u238,negated_conjecture,
    ( k2_tarski(sK1,sK1) != k6_domain_1(u1_struct_0(sK0),sK1)
    | k2_tarski(sK1,sK1) = k6_domain_1(u1_struct_0(sK0),sK1) )).

tff(u237,negated_conjecture,
    ( sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1))
    | sK1 = k2_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

tff(u236,negated_conjecture,
    ( sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1))
    | sK1 = k1_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

tff(u235,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) ) )).

tff(u234,negated_conjecture,
    ( ~ ~ r2_hidden(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u233,negated_conjecture,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0)) )).

tff(u232,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) )).

tff(u231,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) )).

tff(u230,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 )
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 ) )).

tff(u229,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 )
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 ) )).

% (21222)Refutation not found, incomplete strategy% (21222)------------------------------
% (21222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
tff(u228,negated_conjecture,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK1,u1_struct_0(sK0)) )).

% (21222)Termination reason: Refutation not found, incomplete strategy
tff(u227,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u226,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

% (21222)Memory used [KB]: 6140
% (21222)Time elapsed: 0.074 s
tff(u225,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

% (21222)------------------------------
% (21222)------------------------------
tff(u224,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u223,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u222,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

tff(u221,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u220,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u219,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | v3_orders_2(sK0) )).

tff(u218,axiom,(
    ! [X1,X0] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u217,axiom,(
    ! [X1,X0] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u216,negated_conjecture,
    ( ~ v5_orders_2(sK0)
    | v5_orders_2(sK0) )).

tff(u215,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | ~ r1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) )).

tff(u214,axiom,(
    ! [X1,X0] :
      ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u213,negated_conjecture,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK1))
    | r1_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

tff(u212,axiom,(
    ! [X1,X0] :
      ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u211,negated_conjecture,
    ( ~ r2_yellow_0(sK0,k2_tarski(sK1,sK1))
    | r2_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

tff(u210,negated_conjecture,
    ( ~ v4_orders_2(sK0)
    | v4_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:59:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (21233)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (21224)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (21230)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (21219)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (21232)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (21222)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (21235)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.50  % (21224)# SZS output start Saturation.
% 0.22/0.50  tff(u240,negated_conjecture,
% 0.22/0.50      ((~(sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)))) | (sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))))).
% 0.22/0.50  
% 0.22/0.50  tff(u239,negated_conjecture,
% 0.22/0.50      ((~(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK1,sK1)) != k2_tarski(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)))) | (k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK1,sK1)) != k2_tarski(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1))))).
% 0.22/0.50  
% 0.22/0.50  tff(u238,negated_conjecture,
% 0.22/0.50      ((~(k2_tarski(sK1,sK1) = k6_domain_1(u1_struct_0(sK0),sK1))) | (k2_tarski(sK1,sK1) = k6_domain_1(u1_struct_0(sK0),sK1)))).
% 0.22/0.50  
% 0.22/0.50  tff(u237,negated_conjecture,
% 0.22/0.50      ((~(sK1 = k2_yellow_0(sK0,k2_tarski(sK1,sK1)))) | (sK1 = k2_yellow_0(sK0,k2_tarski(sK1,sK1))))).
% 0.22/0.50  
% 0.22/0.50  tff(u236,negated_conjecture,
% 0.22/0.50      ((~(sK1 = k1_yellow_0(sK0,k2_tarski(sK1,sK1)))) | (sK1 = k1_yellow_0(sK0,k2_tarski(sK1,sK1))))).
% 0.22/0.50  
% 0.22/0.50  tff(u235,axiom,
% 0.22/0.50      (![X1, X0] : ((~r2_hidden(X0,X1) | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)))))).
% 0.22/0.50  
% 0.22/0.50  tff(u234,negated_conjecture,
% 0.22/0.50      ((~~r2_hidden(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u233,negated_conjecture,
% 0.22/0.50      ((~r2_hidden(sK1,u1_struct_0(sK0))) | r2_hidden(sK1,u1_struct_0(sK0)))).
% 0.22/0.50  
% 0.22/0.50  tff(u232,axiom,
% 0.22/0.50      (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k2_tarski(X1,X1)) | v1_xboole_0(X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u231,axiom,
% 0.22/0.50      (![X1, X0] : ((~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))))).
% 0.22/0.50  
% 0.22/0.50  tff(u230,negated_conjecture,
% 0.22/0.50      ((~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0))))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0)))))).
% 0.22/0.50  
% 0.22/0.50  tff(u229,negated_conjecture,
% 0.22/0.50      ((~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0))))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0)))))).
% 0.22/0.50  
% 0.22/0.50  % (21222)Refutation not found, incomplete strategy% (21222)------------------------------
% 0.22/0.50  % (21222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  tff(u228,negated_conjecture,
% 0.22/0.50      ((~m1_subset_1(sK1,u1_struct_0(sK0))) | m1_subset_1(sK1,u1_struct_0(sK0)))).
% 0.22/0.50  
% 0.22/0.50  % (21222)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  tff(u227,negated_conjecture,
% 0.22/0.50      ((~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.22/0.50  
% 0.22/0.50  
% 0.22/0.50  tff(u226,axiom,
% 0.22/0.50      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.22/0.50  
% 0.22/0.50  % (21222)Memory used [KB]: 6140
% 0.22/0.50  % (21222)Time elapsed: 0.074 s
% 0.22/0.50  tff(u225,negated_conjecture,
% 0.22/0.50      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.22/0.50  
% 0.22/0.50  % (21222)------------------------------
% 0.22/0.50  % (21222)------------------------------
% 0.22/0.50  tff(u224,negated_conjecture,
% 0.22/0.50      ((~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u223,negated_conjecture,
% 0.22/0.50      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.22/0.50  
% 0.22/0.50  tff(u222,negated_conjecture,
% 0.22/0.50      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.22/0.50  
% 0.22/0.50  tff(u221,axiom,
% 0.22/0.50      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u220,negated_conjecture,
% 0.22/0.50      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.22/0.50  
% 0.22/0.50  tff(u219,negated_conjecture,
% 0.22/0.50      ((~v3_orders_2(sK0)) | v3_orders_2(sK0))).
% 0.22/0.50  
% 0.22/0.50  tff(u218,axiom,
% 0.22/0.50      (![X1, X0] : ((~v5_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | (k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u217,axiom,
% 0.22/0.50      (![X1, X0] : ((~v5_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | (k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u216,negated_conjecture,
% 0.22/0.50      ((~v5_orders_2(sK0)) | v5_orders_2(sK0))).
% 0.22/0.50  
% 0.22/0.50  tff(u215,negated_conjecture,
% 0.22/0.50      ((~~r1_yellow_0(sK0,k5_waybel_0(sK0,sK1))) | ~r1_yellow_0(sK0,k5_waybel_0(sK0,sK1)))).
% 0.22/0.50  
% 0.22/0.50  tff(u214,axiom,
% 0.22/0.50      (![X1, X0] : ((r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u213,negated_conjecture,
% 0.22/0.50      ((~r1_yellow_0(sK0,k2_tarski(sK1,sK1))) | r1_yellow_0(sK0,k2_tarski(sK1,sK1)))).
% 0.22/0.50  
% 0.22/0.50  tff(u212,axiom,
% 0.22/0.50      (![X1, X0] : ((r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u211,negated_conjecture,
% 0.22/0.50      ((~r2_yellow_0(sK0,k2_tarski(sK1,sK1))) | r2_yellow_0(sK0,k2_tarski(sK1,sK1)))).
% 0.22/0.50  
% 0.22/0.50  tff(u210,negated_conjecture,
% 0.22/0.50      ((~v4_orders_2(sK0)) | v4_orders_2(sK0))).
% 0.22/0.50  
% 0.22/0.50  % (21224)# SZS output end Saturation.
% 0.22/0.50  % (21224)------------------------------
% 0.22/0.50  % (21224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (21224)Termination reason: Satisfiable
% 0.22/0.50  
% 0.22/0.50  % (21224)Memory used [KB]: 6268
% 0.22/0.50  % (21224)Time elapsed: 0.056 s
% 0.22/0.50  % (21224)------------------------------
% 0.22/0.50  % (21224)------------------------------
% 0.22/0.50  % (21217)Success in time 0.137 s
%------------------------------------------------------------------------------
