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
% DateTime   : Thu Dec  3 13:16:24 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   34 (  34 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u107,negated_conjecture,
    ( ~ r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1))
    | r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1)) )).

tff(u106,axiom,
    ( ~ ! [X1,X0] :
          ( ~ v1_xboole_0(X1)
          | ~ r2_hidden(X0,X1) )
    | ! [X1,X0] :
        ( ~ v1_xboole_0(X1)
        | ~ r2_hidden(X0,X1) ) )).

tff(u105,negated_conjecture,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | m1_subset_1(sK3,u1_struct_0(sK1)) )).

tff(u104,negated_conjecture,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u103,axiom,
    ( ~ ! [X1,X0,X2] :
          ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
          | ~ m1_subset_1(X2,X0)
          | ~ m1_subset_1(X1,X0)
          | v1_xboole_0(X0) )
    | ! [X1,X0,X2] :
        ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,X0)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) )).

tff(u102,negated_conjecture,
    ( ~ ~ v2_struct_0(sK1)
    | ~ v2_struct_0(sK1) )).

tff(u101,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u100,negated_conjecture,
    ( ~ v4_orders_2(sK0)
    | v4_orders_2(sK0) )).

tff(u99,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u98,negated_conjecture,
    ( ~ v4_yellow_0(sK1,sK0)
    | v4_yellow_0(sK1,sK0) )).

tff(u97,negated_conjecture,
    ( ~ m1_yellow_0(sK1,sK0)
    | m1_yellow_0(sK1,sK0) )).

tff(u96,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) )).

tff(u95,negated_conjecture,
    ( ~ r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:03:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (7274)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  % (7273)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (7275)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.44  % (7276)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.44  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.44  % (7273)# SZS output start Saturation.
% 0.22/0.44  tff(u107,negated_conjecture,
% 0.22/0.44      ((~r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1))) | r2_hidden(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)),u1_struct_0(sK1)))).
% 0.22/0.44  
% 0.22/0.44  tff(u106,axiom,
% 0.22/0.44      ((~(![X1, X0] : ((~v1_xboole_0(X1) | ~r2_hidden(X0,X1))))) | (![X1, X0] : ((~v1_xboole_0(X1) | ~r2_hidden(X0,X1)))))).
% 0.22/0.44  
% 0.22/0.44  tff(u105,negated_conjecture,
% 0.22/0.44      ((~m1_subset_1(sK3,u1_struct_0(sK1))) | m1_subset_1(sK3,u1_struct_0(sK1)))).
% 0.22/0.44  
% 0.22/0.44  tff(u104,negated_conjecture,
% 0.22/0.44      ((~m1_subset_1(sK2,u1_struct_0(sK1))) | m1_subset_1(sK2,u1_struct_0(sK1)))).
% 0.22/0.44  
% 0.22/0.44  tff(u103,axiom,
% 0.22/0.44      ((~(![X1, X0, X2] : ((m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))))) | (![X1, X0, X2] : ((m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)))))).
% 0.22/0.44  
% 0.22/0.44  tff(u102,negated_conjecture,
% 0.22/0.44      ((~~v2_struct_0(sK1)) | ~v2_struct_0(sK1))).
% 0.22/0.44  
% 0.22/0.44  tff(u101,negated_conjecture,
% 0.22/0.44      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.22/0.44  
% 0.22/0.44  tff(u100,negated_conjecture,
% 0.22/0.44      ((~v4_orders_2(sK0)) | v4_orders_2(sK0))).
% 0.22/0.44  
% 0.22/0.44  tff(u99,negated_conjecture,
% 0.22/0.44      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.22/0.44  
% 0.22/0.44  tff(u98,negated_conjecture,
% 0.22/0.44      ((~v4_yellow_0(sK1,sK0)) | v4_yellow_0(sK1,sK0))).
% 0.22/0.44  
% 0.22/0.44  tff(u97,negated_conjecture,
% 0.22/0.44      ((~m1_yellow_0(sK1,sK0)) | m1_yellow_0(sK1,sK0))).
% 0.22/0.44  
% 0.22/0.44  tff(u96,negated_conjecture,
% 0.22/0.44      ((~~r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))) | ~r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)))).
% 0.22/0.44  
% 0.22/0.44  tff(u95,negated_conjecture,
% 0.22/0.44      ((~r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))) | r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)))).
% 0.22/0.44  
% 0.22/0.44  % (7273)# SZS output end Saturation.
% 0.22/0.44  % (7273)------------------------------
% 0.22/0.44  % (7273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (7273)Termination reason: Satisfiable
% 0.22/0.44  
% 0.22/0.44  % (7273)Memory used [KB]: 10618
% 0.22/0.44  % (7273)Time elapsed: 0.004 s
% 0.22/0.44  % (7273)------------------------------
% 0.22/0.44  % (7273)------------------------------
% 0.22/0.44  % (7267)Success in time 0.08 s
%------------------------------------------------------------------------------
