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
% DateTime   : Thu Dec  3 13:16:56 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u32,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u31,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u30,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u29,negated_conjecture,(
    l1_waybel_0(sK1,sK0) )).

tff(u28,negated_conjecture,
    ( ~ ~ v10_waybel_0(sK1,sK0)
    | ~ v10_waybel_0(sK1,sK0) )).

tff(u27,negated_conjecture,
    ( ~ ~ v10_waybel_0(sK1,sK0)
    | ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK1))
        | m1_subset_1(sK3(X2),u1_struct_0(sK1)) ) )).

tff(u26,negated_conjecture,
    ( ~ ~ v10_waybel_0(sK1,sK0)
    | ! [X2,X4] :
        ( ~ r1_orders_2(sK1,sK3(X2),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X2),k2_waybel_0(sK0,sK1,X4)) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:13:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (18761)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.47  % (18754)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.47  % (18759)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.47  % (18752)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.47  % (18752)Refutation not found, incomplete strategy% (18752)------------------------------
% 0.21/0.47  % (18752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (18752)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (18752)Memory used [KB]: 895
% 0.21/0.47  % (18752)Time elapsed: 0.077 s
% 0.21/0.47  % (18752)------------------------------
% 0.21/0.47  % (18752)------------------------------
% 0.21/0.48  % (18762)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.48  % (18762)Refutation not found, incomplete strategy% (18762)------------------------------
% 0.21/0.48  % (18762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (18762)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (18762)Memory used [KB]: 5373
% 0.21/0.48  % (18762)Time elapsed: 0.006 s
% 0.21/0.48  % (18762)------------------------------
% 0.21/0.48  % (18762)------------------------------
% 0.21/0.48  % (18753)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.48  % (18753)# SZS output start Saturation.
% 0.21/0.48  tff(u32,negated_conjecture,
% 0.21/0.48      ~v2_struct_0(sK1)).
% 0.21/0.48  
% 0.21/0.48  tff(u31,negated_conjecture,
% 0.21/0.48      ~v2_struct_0(sK0)).
% 0.21/0.48  
% 0.21/0.48  tff(u30,negated_conjecture,
% 0.21/0.48      l1_orders_2(sK0)).
% 0.21/0.48  
% 0.21/0.48  tff(u29,negated_conjecture,
% 0.21/0.48      l1_waybel_0(sK1,sK0)).
% 0.21/0.48  
% 0.21/0.48  tff(u28,negated_conjecture,
% 0.21/0.48      ((~~v10_waybel_0(sK1,sK0)) | ~v10_waybel_0(sK1,sK0))).
% 0.21/0.48  
% 0.21/0.48  tff(u27,negated_conjecture,
% 0.21/0.48      ((~~v10_waybel_0(sK1,sK0)) | (![X2] : ((~m1_subset_1(X2,u1_struct_0(sK1)) | m1_subset_1(sK3(X2),u1_struct_0(sK1))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u26,negated_conjecture,
% 0.21/0.48      ((~~v10_waybel_0(sK1,sK0)) | (![X2, X4] : ((~r1_orders_2(sK1,sK3(X2),X4) | ~m1_subset_1(X4,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X2),k2_waybel_0(sK0,sK1,X4))))))).
% 0.21/0.48  
% 0.21/0.48  % (18753)# SZS output end Saturation.
% 0.21/0.48  % (18753)------------------------------
% 0.21/0.48  % (18753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (18753)Termination reason: Satisfiable
% 0.21/0.48  
% 0.21/0.48  % (18753)Memory used [KB]: 5245
% 0.21/0.48  % (18753)Time elapsed: 0.005 s
% 0.21/0.48  % (18753)------------------------------
% 0.21/0.48  % (18753)------------------------------
% 0.21/0.48  % (18741)Success in time 0.126 s
%------------------------------------------------------------------------------
