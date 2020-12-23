%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:13 EST 2020

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
    ( ~ ( sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) )
    | sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) )).

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

tff(u228,negated_conjecture,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u227,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u226,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u225,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

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

tff(u215,axiom,(
    ! [X1,X0] :
      ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u214,negated_conjecture,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK1))
    | r1_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

tff(u213,negated_conjecture,
    ( ~ ~ r2_yellow_0(sK0,k6_waybel_0(sK0,sK1))
    | ~ r2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) )).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:12:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (4453)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.45  % (4453)Refutation not found, incomplete strategy% (4453)------------------------------
% 0.22/0.45  % (4453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (4453)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.45  
% 0.22/0.45  % (4453)Memory used [KB]: 6140
% 0.22/0.45  % (4453)Time elapsed: 0.008 s
% 0.22/0.45  % (4453)------------------------------
% 0.22/0.45  % (4453)------------------------------
% 0.22/0.46  % (4449)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (4464)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (4465)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (4456)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (4460)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.48  % (4456)# SZS output start Saturation.
% 0.22/0.48  tff(u240,negated_conjecture,
% 0.22/0.48      ((~(sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)))) | (sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1))))).
% 0.22/0.48  
% 0.22/0.48  tff(u239,negated_conjecture,
% 0.22/0.48      ((~(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK1,sK1)) != k2_tarski(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)))) | (k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k2_tarski(sK1,sK1)) != k2_tarski(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1))))).
% 0.22/0.48  
% 0.22/0.48  tff(u238,negated_conjecture,
% 0.22/0.48      ((~(k2_tarski(sK1,sK1) = k6_domain_1(u1_struct_0(sK0),sK1))) | (k2_tarski(sK1,sK1) = k6_domain_1(u1_struct_0(sK0),sK1)))).
% 0.22/0.48  
% 0.22/0.48  tff(u237,negated_conjecture,
% 0.22/0.48      ((~(sK1 = k2_yellow_0(sK0,k2_tarski(sK1,sK1)))) | (sK1 = k2_yellow_0(sK0,k2_tarski(sK1,sK1))))).
% 0.22/0.48  
% 0.22/0.48  tff(u236,negated_conjecture,
% 0.22/0.48      ((~(sK1 = k1_yellow_0(sK0,k2_tarski(sK1,sK1)))) | (sK1 = k1_yellow_0(sK0,k2_tarski(sK1,sK1))))).
% 0.22/0.48  
% 0.22/0.48  tff(u235,axiom,
% 0.22/0.48      (![X1, X0] : ((~r2_hidden(X0,X1) | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)))))).
% 0.22/0.48  
% 0.22/0.48  tff(u234,negated_conjecture,
% 0.22/0.48      ((~~r2_hidden(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u233,negated_conjecture,
% 0.22/0.48      ((~r2_hidden(sK1,u1_struct_0(sK0))) | r2_hidden(sK1,u1_struct_0(sK0)))).
% 0.22/0.48  
% 0.22/0.48  tff(u232,axiom,
% 0.22/0.48      (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k2_tarski(X1,X1)) | v1_xboole_0(X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u231,axiom,
% 0.22/0.48      (![X1, X0] : ((~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))))).
% 0.22/0.48  
% 0.22/0.48  tff(u230,negated_conjecture,
% 0.22/0.48      ((~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0))))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0)))))).
% 0.22/0.48  
% 0.22/0.48  tff(u229,negated_conjecture,
% 0.22/0.48      ((~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0))))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0)))))).
% 0.22/0.48  
% 0.22/0.48  tff(u228,negated_conjecture,
% 0.22/0.48      ((~m1_subset_1(sK1,u1_struct_0(sK0))) | m1_subset_1(sK1,u1_struct_0(sK0)))).
% 0.22/0.48  
% 0.22/0.48  tff(u227,negated_conjecture,
% 0.22/0.48      ((~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u226,axiom,
% 0.22/0.48      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u225,negated_conjecture,
% 0.22/0.48      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.22/0.48  
% 0.22/0.48  tff(u224,negated_conjecture,
% 0.22/0.48      ((~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u223,negated_conjecture,
% 0.22/0.48      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.22/0.48  
% 0.22/0.48  tff(u222,negated_conjecture,
% 0.22/0.48      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.22/0.48  
% 0.22/0.48  tff(u221,axiom,
% 0.22/0.48      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u220,negated_conjecture,
% 0.22/0.48      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.22/0.48  
% 0.22/0.48  tff(u219,negated_conjecture,
% 0.22/0.48      ((~v3_orders_2(sK0)) | v3_orders_2(sK0))).
% 0.22/0.48  
% 0.22/0.48  tff(u218,axiom,
% 0.22/0.48      (![X1, X0] : ((~v5_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | (k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u217,axiom,
% 0.22/0.48      (![X1, X0] : ((~v5_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | (k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u216,negated_conjecture,
% 0.22/0.48      ((~v5_orders_2(sK0)) | v5_orders_2(sK0))).
% 0.22/0.48  
% 0.22/0.48  tff(u215,axiom,
% 0.22/0.48      (![X1, X0] : ((r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u214,negated_conjecture,
% 0.22/0.48      ((~r1_yellow_0(sK0,k2_tarski(sK1,sK1))) | r1_yellow_0(sK0,k2_tarski(sK1,sK1)))).
% 0.22/0.48  
% 0.22/0.48  tff(u213,negated_conjecture,
% 0.22/0.48      ((~~r2_yellow_0(sK0,k6_waybel_0(sK0,sK1))) | ~r2_yellow_0(sK0,k6_waybel_0(sK0,sK1)))).
% 0.22/0.48  
% 0.22/0.48  tff(u212,axiom,
% 0.22/0.48      (![X1, X0] : ((r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u211,negated_conjecture,
% 0.22/0.48      ((~r2_yellow_0(sK0,k2_tarski(sK1,sK1))) | r2_yellow_0(sK0,k2_tarski(sK1,sK1)))).
% 0.22/0.48  
% 0.22/0.48  tff(u210,negated_conjecture,
% 0.22/0.48      ((~v4_orders_2(sK0)) | v4_orders_2(sK0))).
% 0.22/0.48  
% 0.22/0.48  % (4456)# SZS output end Saturation.
% 0.22/0.48  % (4456)------------------------------
% 0.22/0.48  % (4456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (4456)Termination reason: Satisfiable
% 0.22/0.48  % (4452)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  
% 0.22/0.48  % (4456)Memory used [KB]: 6268
% 0.22/0.48  % (4456)Time elapsed: 0.003 s
% 0.22/0.48  % (4456)------------------------------
% 0.22/0.48  % (4456)------------------------------
% 0.22/0.48  % (4444)Success in time 0.121 s
%------------------------------------------------------------------------------
