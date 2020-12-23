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
% DateTime   : Thu Dec  3 13:16:07 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :    8 (   8 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    0
%              Number of atoms          :   26 (  26 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u80,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k2_tarski(sK1,sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

tff(u79,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u78,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

tff(u77,axiom,
    ( ~ ! [X0] :
          ( ~ v1_xboole_0(u1_struct_0(X0))
          | ~ l1_struct_0(X0)
          | v2_struct_0(X0) )
    | ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) )).

tff(u76,axiom,
    ( ~ ! [X0] :
          ( ~ l1_orders_2(X0)
          | l1_struct_0(X0) )
    | ! [X0] :
        ( ~ l1_orders_2(X0)
        | l1_struct_0(X0) ) )).

tff(u75,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u74,axiom,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(X1,X0)
          | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
          | v1_xboole_0(X0) )
    | ! [X1,X0] :
        ( ~ m1_subset_1(X1,X0)
        | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
        | v1_xboole_0(X0) ) )).

tff(u73,negated_conjecture,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK1,u1_struct_0(sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (9291)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (9290)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (9288)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (9299)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (9298)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.48  % (9290)# SZS output start Saturation.
% 0.20/0.48  tff(u80,negated_conjecture,
% 0.20/0.48      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)))).
% 0.20/0.48  
% 0.20/0.48  tff(u79,negated_conjecture,
% 0.20/0.48      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.20/0.48  
% 0.20/0.48  tff(u78,negated_conjecture,
% 0.20/0.48      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.20/0.48  
% 0.20/0.48  tff(u77,axiom,
% 0.20/0.48      ((~(![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))) | (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)))))).
% 0.20/0.48  
% 0.20/0.48  tff(u76,axiom,
% 0.20/0.48      ((~(![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))) | (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0)))))).
% 0.20/0.48  
% 0.20/0.48  tff(u75,negated_conjecture,
% 0.20/0.48      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.20/0.48  
% 0.20/0.48  tff(u74,axiom,
% 0.20/0.48      ((~(![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k2_tarski(X1,X1)) | v1_xboole_0(X0))))) | (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k2_tarski(X1,X1)) | v1_xboole_0(X0)))))).
% 0.20/0.48  
% 0.20/0.48  tff(u73,negated_conjecture,
% 0.20/0.48      ((~m1_subset_1(sK1,u1_struct_0(sK0))) | m1_subset_1(sK1,u1_struct_0(sK0)))).
% 0.20/0.48  
% 0.20/0.48  % (9290)# SZS output end Saturation.
% 0.20/0.48  % (9290)------------------------------
% 0.20/0.48  % (9290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (9290)Termination reason: Satisfiable
% 0.20/0.48  
% 0.20/0.48  % (9290)Memory used [KB]: 6140
% 0.20/0.48  % (9290)Time elapsed: 0.063 s
% 0.20/0.48  % (9290)------------------------------
% 0.20/0.48  % (9290)------------------------------
% 0.20/0.48  % (9296)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (9282)Success in time 0.126 s
%------------------------------------------------------------------------------
