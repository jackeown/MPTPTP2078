%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:02 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    0
%              Number of atoms          :   25 (  25 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u49,negated_conjecture,(
    ~ r1_tarski(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1)) )).

tff(u48,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u47,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) )).

tff(u46,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) )).

tff(u45,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) )).

tff(u44,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u43,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u42,negated_conjecture,(
    v4_orders_2(sK0) )).

tff(u41,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u40,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u39,negated_conjecture,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,X0,sK1)
      | r1_orders_2(sK0,X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u38,negated_conjecture,(
    r1_orders_2(sK0,sK1,sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:37:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (29029)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (29024)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (29020)WARNING: option uwaf not known.
% 0.21/0.51  % (29020)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.21/0.51  % (29014)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.51  % (29013)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.51  % (29019)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.52  % (29019)Refutation not found, incomplete strategy% (29019)------------------------------
% 0.21/0.52  % (29019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29019)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29019)Memory used [KB]: 9850
% 0.21/0.52  % (29019)Time elapsed: 0.079 s
% 0.21/0.52  % (29019)------------------------------
% 0.21/0.52  % (29019)------------------------------
% 0.21/0.52  % (29017)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (29017)# SZS output start Saturation.
% 0.21/0.52  tff(u49,negated_conjecture,
% 0.21/0.52      ~r1_tarski(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1))).
% 0.21/0.52  
% 0.21/0.52  tff(u48,axiom,
% 0.21/0.52      (![X0] : (r1_tarski(X0,X0)))).
% 0.21/0.52  
% 0.21/0.52  tff(u47,axiom,
% 0.21/0.52      (![X1, X0] : ((~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u46,axiom,
% 0.21/0.52      (![X1, X0] : ((r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u45,axiom,
% 0.21/0.52      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1))))).
% 0.21/0.52  
% 0.21/0.52  tff(u44,negated_conjecture,
% 0.21/0.52      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  tff(u43,negated_conjecture,
% 0.21/0.52      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  tff(u42,negated_conjecture,
% 0.21/0.52      v4_orders_2(sK0)).
% 0.21/0.52  
% 0.21/0.52  tff(u41,negated_conjecture,
% 0.21/0.52      l1_orders_2(sK0)).
% 0.21/0.52  
% 0.21/0.52  tff(u40,axiom,
% 0.21/0.52      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.21/0.52  
% 0.21/0.52  tff(u39,negated_conjecture,
% 0.21/0.52      (![X0] : ((~r1_orders_2(sK0,X0,sK1) | r1_orders_2(sK0,X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)))))).
% 0.21/0.52  
% 0.21/0.52  tff(u38,negated_conjecture,
% 0.21/0.52      r1_orders_2(sK0,sK1,sK2)).
% 0.21/0.52  
% 0.21/0.52  % (29017)# SZS output end Saturation.
% 0.21/0.52  % (29017)------------------------------
% 0.21/0.52  % (29017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29017)Termination reason: Satisfiable
% 0.21/0.52  
% 0.21/0.52  % (29017)Memory used [KB]: 5373
% 0.21/0.52  % (29017)Time elapsed: 0.106 s
% 0.21/0.52  % (29017)------------------------------
% 0.21/0.52  % (29017)------------------------------
% 0.21/0.52  % (29013)Refutation not found, incomplete strategy% (29013)------------------------------
% 0.21/0.52  % (29013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29013)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29013)Memory used [KB]: 9850
% 0.21/0.52  % (29013)Time elapsed: 0.077 s
% 0.21/0.52  % (29013)------------------------------
% 0.21/0.52  % (29013)------------------------------
% 0.21/0.52  % (29015)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.52  % (29008)Success in time 0.162 s
%------------------------------------------------------------------------------
