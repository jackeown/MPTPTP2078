%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:01 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    0
%              Number of atoms          :   35 (  35 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u50,negated_conjecture,(
    ~ r1_tarski(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)) )).

tff(u49,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK3(X0,X1),X2)
      | r1_tarski(X0,X1) ) )).

tff(u48,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u47,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) )).

tff(u46,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) )).

tff(u45,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) )).

tff(u44,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) )).

tff(u43,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK3(X0,X2),X1)
      | r1_tarski(X0,X2) ) )).

tff(u42,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u41,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u40,negated_conjecture,(
    v4_orders_2(sK0) )).

tff(u39,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u38,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3) ) )).

tff(u37,negated_conjecture,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,sK1,X0) ) )).

tff(u36,negated_conjecture,(
    r1_orders_2(sK0,sK1,sK2) )).

tff(u35,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:46:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (30223)WARNING: option uwaf not known.
% 0.20/0.46  % (30230)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.20/0.46  % (30230)Refutation not found, incomplete strategy% (30230)------------------------------
% 0.20/0.46  % (30230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (30223)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.20/0.46  % (30230)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (30230)Memory used [KB]: 9850
% 0.20/0.46  % (30230)Time elapsed: 0.058 s
% 0.20/0.46  % (30230)------------------------------
% 0.20/0.46  % (30230)------------------------------
% 0.20/0.46  % (30218)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.47  % (30214)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.20/0.48  % (30226)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.48  % (30219)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.48  % (30219)# SZS output start Saturation.
% 0.20/0.48  tff(u50,negated_conjecture,
% 0.20/0.48      ~r1_tarski(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2))).
% 0.20/0.48  
% 0.20/0.48  tff(u49,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~r1_tarski(X0,X2) | r2_hidden(sK3(X0,X1),X2) | r1_tarski(X0,X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u48,axiom,
% 0.20/0.48      (![X0] : (r1_tarski(X0,X0)))).
% 0.20/0.48  
% 0.20/0.48  tff(u47,axiom,
% 0.20/0.48      (![X1, X0] : ((~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u46,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))))).
% 0.20/0.48  
% 0.20/0.48  tff(u45,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u44,axiom,
% 0.20/0.48      (![X1, X0] : ((r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u43,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK3(X0,X2),X1) | r1_tarski(X0,X2))))).
% 0.20/0.48  
% 0.20/0.48  tff(u42,negated_conjecture,
% 0.20/0.48      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.48  
% 0.20/0.48  tff(u41,negated_conjecture,
% 0.20/0.48      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.20/0.48  
% 0.20/0.48  tff(u40,negated_conjecture,
% 0.20/0.48      v4_orders_2(sK0)).
% 0.20/0.48  
% 0.20/0.48  tff(u39,negated_conjecture,
% 0.20/0.48      l1_orders_2(sK0)).
% 0.20/0.48  
% 0.20/0.48  tff(u38,axiom,
% 0.20/0.48      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v4_orders_2(X0) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X1,X3))))).
% 0.20/0.48  
% 0.20/0.48  tff(u37,negated_conjecture,
% 0.20/0.48      (![X0] : ((~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X0))))).
% 0.20/0.48  
% 0.20/0.48  tff(u36,negated_conjecture,
% 0.20/0.48      r1_orders_2(sK0,sK1,sK2)).
% 0.20/0.48  
% 0.20/0.48  tff(u35,negated_conjecture,
% 0.20/0.48      ~v2_struct_0(sK0)).
% 0.20/0.48  
% 0.20/0.48  % (30219)# SZS output end Saturation.
% 0.20/0.48  % (30219)------------------------------
% 0.20/0.48  % (30219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (30219)Termination reason: Satisfiable
% 0.20/0.48  
% 0.20/0.48  % (30219)Memory used [KB]: 5373
% 0.20/0.48  % (30219)Time elapsed: 0.028 s
% 0.20/0.48  % (30219)------------------------------
% 0.20/0.48  % (30219)------------------------------
% 0.20/0.48  % (30212)Success in time 0.126 s
%------------------------------------------------------------------------------
