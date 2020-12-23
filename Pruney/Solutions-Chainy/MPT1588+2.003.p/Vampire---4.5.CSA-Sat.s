%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:24 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    0
%              Number of atoms          :   36 (  36 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u100,negated_conjecture,
    ( ~ ( k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) )
    | k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) )).

tff(u99,negated_conjecture,
    ( ~ ~ v2_struct_0(sK1)
    | ~ v2_struct_0(sK1) )).

tff(u98,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u97,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

tff(u96,axiom,
    ( ~ ! [X0] :
          ( ~ v1_xboole_0(u1_struct_0(X0))
          | ~ l1_struct_0(X0)
          | v2_struct_0(X0) )
    | ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) )).

tff(u95,negated_conjecture,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | m1_subset_1(sK3,u1_struct_0(sK1)) )).

tff(u94,negated_conjecture,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u93,axiom,
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

tff(u92,axiom,
    ( ~ ! [X0] :
          ( ~ l1_orders_2(X0)
          | l1_struct_0(X0) )
    | ! [X0] :
        ( ~ l1_orders_2(X0)
        | l1_struct_0(X0) ) )).

tff(u91,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u90,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) )).

tff(u89,negated_conjecture,
    ( ~ r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.40  % (26340)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.41  % (26339)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % (26343)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.42  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.42  % (26343)# SZS output start Saturation.
% 0.20/0.42  tff(u100,negated_conjecture,
% 0.20/0.42      ((~(k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)))) | (k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)) != k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))))).
% 0.20/0.42  
% 0.20/0.42  tff(u99,negated_conjecture,
% 0.20/0.42      ((~~v2_struct_0(sK1)) | ~v2_struct_0(sK1))).
% 0.20/0.42  
% 0.20/0.42  tff(u98,negated_conjecture,
% 0.20/0.42      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.20/0.42  
% 0.20/0.42  tff(u97,negated_conjecture,
% 0.20/0.42      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.20/0.42  
% 0.20/0.42  tff(u96,axiom,
% 0.20/0.42      ((~(![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))) | (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)))))).
% 0.20/0.42  
% 0.20/0.42  tff(u95,negated_conjecture,
% 0.20/0.42      ((~m1_subset_1(sK3,u1_struct_0(sK1))) | m1_subset_1(sK3,u1_struct_0(sK1)))).
% 0.20/0.42  
% 0.20/0.42  tff(u94,negated_conjecture,
% 0.20/0.42      ((~m1_subset_1(sK2,u1_struct_0(sK1))) | m1_subset_1(sK2,u1_struct_0(sK1)))).
% 0.20/0.42  
% 0.20/0.42  tff(u93,axiom,
% 0.20/0.42      ((~(![X1, X0, X2] : ((m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))))) | (![X1, X0, X2] : ((m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)))))).
% 0.20/0.42  
% 0.20/0.42  tff(u92,axiom,
% 0.20/0.42      ((~(![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))) | (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0)))))).
% 0.20/0.42  
% 0.20/0.42  tff(u91,negated_conjecture,
% 0.20/0.42      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.20/0.42  
% 0.20/0.42  tff(u90,negated_conjecture,
% 0.20/0.42      ((~~r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))) | ~r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3)))).
% 0.20/0.42  
% 0.20/0.42  tff(u89,negated_conjecture,
% 0.20/0.42      ((~r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3))) | r1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK1),sK2,sK3)))).
% 0.20/0.42  
% 0.20/0.42  % (26343)# SZS output end Saturation.
% 0.20/0.42  % (26343)------------------------------
% 0.20/0.42  % (26343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (26343)Termination reason: Satisfiable
% 0.20/0.42  
% 0.20/0.42  % (26343)Memory used [KB]: 6140
% 0.20/0.42  % (26343)Time elapsed: 0.004 s
% 0.20/0.42  % (26343)------------------------------
% 0.20/0.42  % (26343)------------------------------
% 0.20/0.42  % (26342)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.43  % (26332)Success in time 0.073 s
%------------------------------------------------------------------------------
