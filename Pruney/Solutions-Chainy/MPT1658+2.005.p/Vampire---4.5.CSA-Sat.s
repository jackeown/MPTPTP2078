%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:12 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    0
%              Number of atoms          :   62 (  62 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u98,negated_conjecture,
    ( ~ ( k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k4_waybel_0(sK0,sK1)) )
    | k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k4_waybel_0(sK0,sK1)) )).

tff(u97,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u96,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ l1_orders_2(X0)
          | r1_lattice3(X0,X2,sK2(X0,X1,X2))
          | r1_lattice3(X0,X1,sK2(X0,X1,X2))
          | ~ r2_yellow_0(X0,X1)
          | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | v2_struct_0(X0) )
    | ! [X1,X0,X2] :
        ( ~ l1_orders_2(X0)
        | r1_lattice3(X0,X2,sK2(X0,X1,X2))
        | r1_lattice3(X0,X1,sK2(X0,X1,X2))
        | ~ r2_yellow_0(X0,X1)
        | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
        | v2_struct_0(X0) ) )).

tff(u95,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u94,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ r2_yellow_0(sK0,X1)
          | r1_lattice3(sK0,X1,sK2(sK0,X1,X0))
          | r1_lattice3(sK0,X0,sK2(sK0,X1,X0))
          | k2_yellow_0(sK0,X1) = k2_yellow_0(sK0,X0) )
    | ! [X1,X0] :
        ( ~ r2_yellow_0(sK0,X1)
        | r1_lattice3(sK0,X1,sK2(sK0,X1,X0))
        | r1_lattice3(sK0,X0,sK2(sK0,X1,X0))
        | k2_yellow_0(sK0,X1) = k2_yellow_0(sK0,X0) ) )).

tff(u93,negated_conjecture,
    ( ~ r2_yellow_0(sK0,sK1)
    | r2_yellow_0(sK0,sK1) )).

tff(u92,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u91,axiom,
    ( ~ ! [X1,X0,X2] :
          ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
          | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ l1_orders_2(X0)
          | v2_struct_0(X0) )
    | ! [X1,X0,X2] :
        ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
        | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
        | ~ r2_yellow_0(X0,X1)
        | ~ l1_orders_2(X0)
        | v2_struct_0(X0) ) )).

tff(u90,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
          | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2))
          | ~ r2_yellow_0(X0,X1)
          | ~ l1_orders_2(X0)
          | v2_struct_0(X0) )
    | ! [X1,X0,X2] :
        ( ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
        | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
        | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2))
        | ~ r2_yellow_0(X0,X1)
        | ~ l1_orders_2(X0)
        | v2_struct_0(X0) ) )).

tff(u89,negated_conjecture,
    ( ~ ! [X0] :
          ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,X0))
          | r1_lattice3(sK0,X0,sK2(sK0,sK1,X0))
          | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,X0) )
    | ! [X0] :
        ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,X0))
        | r1_lattice3(sK0,X0,sK2(sK0,sK1,X0))
        | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,X0) ) )).

tff(u88,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | v3_orders_2(sK0) )).

tff(u87,negated_conjecture,
    ( ~ v4_orders_2(sK0)
    | v4_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:24:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (28078)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.43  % (28077)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  % (28079)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.44  % (28076)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.44  % (28076)# SZS output start Saturation.
% 0.22/0.44  tff(u98,negated_conjecture,
% 0.22/0.44      ((~(k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k4_waybel_0(sK0,sK1)))) | (k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k4_waybel_0(sK0,sK1))))).
% 0.22/0.44  
% 0.22/0.44  tff(u97,negated_conjecture,
% 0.22/0.44      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.22/0.44  
% 0.22/0.44  tff(u96,axiom,
% 0.22/0.44      ((~(![X1, X0, X2] : ((~l1_orders_2(X0) | r1_lattice3(X0,X2,sK2(X0,X1,X2)) | r1_lattice3(X0,X1,sK2(X0,X1,X2)) | ~r2_yellow_0(X0,X1) | (k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)) | v2_struct_0(X0))))) | (![X1, X0, X2] : ((~l1_orders_2(X0) | r1_lattice3(X0,X2,sK2(X0,X1,X2)) | r1_lattice3(X0,X1,sK2(X0,X1,X2)) | ~r2_yellow_0(X0,X1) | (k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)) | v2_struct_0(X0)))))).
% 0.22/0.44  
% 0.22/0.44  tff(u95,negated_conjecture,
% 0.22/0.44      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.22/0.44  
% 0.22/0.44  tff(u94,negated_conjecture,
% 0.22/0.44      ((~(![X1, X0] : ((~r2_yellow_0(sK0,X1) | r1_lattice3(sK0,X1,sK2(sK0,X1,X0)) | r1_lattice3(sK0,X0,sK2(sK0,X1,X0)) | (k2_yellow_0(sK0,X1) = k2_yellow_0(sK0,X0)))))) | (![X1, X0] : ((~r2_yellow_0(sK0,X1) | r1_lattice3(sK0,X1,sK2(sK0,X1,X0)) | r1_lattice3(sK0,X0,sK2(sK0,X1,X0)) | (k2_yellow_0(sK0,X1) = k2_yellow_0(sK0,X0))))))).
% 0.22/0.44  
% 0.22/0.44  tff(u93,negated_conjecture,
% 0.22/0.44      ((~r2_yellow_0(sK0,sK1)) | r2_yellow_0(sK0,sK1))).
% 0.22/0.44  
% 0.22/0.44  tff(u92,negated_conjecture,
% 0.22/0.44      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.22/0.44  
% 0.22/0.44  tff(u91,axiom,
% 0.22/0.44      ((~(![X1, X0, X2] : ((m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | (k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)) | ~r2_yellow_0(X0,X1) | ~l1_orders_2(X0) | v2_struct_0(X0))))) | (![X1, X0, X2] : ((m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | (k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)) | ~r2_yellow_0(X0,X1) | ~l1_orders_2(X0) | v2_struct_0(X0)))))).
% 0.22/0.44  
% 0.22/0.44  tff(u90,axiom,
% 0.22/0.44      ((~(![X1, X0, X2] : ((~r1_lattice3(X0,X2,sK2(X0,X1,X2)) | (k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)) | ~r1_lattice3(X0,X1,sK2(X0,X1,X2)) | ~r2_yellow_0(X0,X1) | ~l1_orders_2(X0) | v2_struct_0(X0))))) | (![X1, X0, X2] : ((~r1_lattice3(X0,X2,sK2(X0,X1,X2)) | (k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)) | ~r1_lattice3(X0,X1,sK2(X0,X1,X2)) | ~r2_yellow_0(X0,X1) | ~l1_orders_2(X0) | v2_struct_0(X0)))))).
% 0.22/0.44  
% 0.22/0.44  tff(u89,negated_conjecture,
% 0.22/0.44      ((~(![X0] : ((r1_lattice3(sK0,sK1,sK2(sK0,sK1,X0)) | r1_lattice3(sK0,X0,sK2(sK0,sK1,X0)) | (k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,X0)))))) | (![X0] : ((r1_lattice3(sK0,sK1,sK2(sK0,sK1,X0)) | r1_lattice3(sK0,X0,sK2(sK0,sK1,X0)) | (k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,X0))))))).
% 0.22/0.44  
% 0.22/0.44  tff(u88,negated_conjecture,
% 0.22/0.44      ((~v3_orders_2(sK0)) | v3_orders_2(sK0))).
% 0.22/0.44  
% 0.22/0.44  tff(u87,negated_conjecture,
% 0.22/0.44      ((~v4_orders_2(sK0)) | v4_orders_2(sK0))).
% 0.22/0.44  
% 0.22/0.44  % (28076)# SZS output end Saturation.
% 0.22/0.44  % (28076)------------------------------
% 0.22/0.44  % (28076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (28076)Termination reason: Satisfiable
% 0.22/0.44  
% 0.22/0.44  % (28076)Memory used [KB]: 10618
% 0.22/0.44  % (28076)Time elapsed: 0.004 s
% 0.22/0.44  % (28076)------------------------------
% 0.22/0.44  % (28076)------------------------------
% 0.22/0.44  % (28070)Success in time 0.076 s
%------------------------------------------------------------------------------
