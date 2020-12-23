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
% DateTime   : Thu Dec  3 13:16:22 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    0
%              Number of atoms          :   22 (  22 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u47,negated_conjecture,(
    sK2 = sK4 )).

tff(u46,negated_conjecture,(
    sK3 = sK5 )).

tff(u45,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) )).

tff(u44,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u43,negated_conjecture,(
    m1_subset_1(sK3,u1_struct_0(sK0)) )).

tff(u42,negated_conjecture,(
    m1_subset_1(sK3,u1_struct_0(sK1)) )).

tff(u41,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u40,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u39,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u38,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u37,negated_conjecture,(
    ~ r1_orders_2(sK0,sK2,sK3) )).

tff(u36,negated_conjecture,(
    r1_orders_2(sK1,sK2,sK3) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:18:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (29498)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.42  % (29505)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.42  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.42  % (29505)# SZS output start Saturation.
% 0.21/0.42  tff(u47,negated_conjecture,
% 0.21/0.42      (sK2 = sK4)).
% 0.21/0.42  
% 0.21/0.42  tff(u46,negated_conjecture,
% 0.21/0.42      (sK3 = sK5)).
% 0.21/0.42  
% 0.21/0.42  tff(u45,axiom,
% 0.21/0.42      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0))))).
% 0.21/0.42  
% 0.21/0.42  tff(u44,negated_conjecture,
% 0.21/0.42      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.21/0.42  
% 0.21/0.42  tff(u43,negated_conjecture,
% 0.21/0.42      m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.21/0.42  
% 0.21/0.42  tff(u42,negated_conjecture,
% 0.21/0.42      m1_subset_1(sK3,u1_struct_0(sK1))).
% 0.21/0.42  
% 0.21/0.42  tff(u41,negated_conjecture,
% 0.21/0.42      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.21/0.42  
% 0.21/0.42  tff(u40,axiom,
% 0.21/0.42      (![X1, X0, X2] : ((~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.42  
% 0.21/0.42  tff(u39,axiom,
% 0.21/0.42      (![X1, X0, X2] : ((r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.42  
% 0.21/0.42  tff(u38,negated_conjecture,
% 0.21/0.42      l1_orders_2(sK0)).
% 0.21/0.42  
% 0.21/0.42  tff(u37,negated_conjecture,
% 0.21/0.42      ~r1_orders_2(sK0,sK2,sK3)).
% 0.21/0.42  
% 0.21/0.42  tff(u36,negated_conjecture,
% 0.21/0.42      r1_orders_2(sK1,sK2,sK3)).
% 0.21/0.42  
% 0.21/0.42  % (29505)# SZS output end Saturation.
% 0.21/0.42  % (29505)------------------------------
% 0.21/0.42  % (29505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (29505)Termination reason: Satisfiable
% 0.21/0.42  
% 0.21/0.42  % (29505)Memory used [KB]: 10618
% 0.21/0.42  % (29505)Time elapsed: 0.004 s
% 0.21/0.42  % (29505)------------------------------
% 0.21/0.42  % (29505)------------------------------
% 0.21/0.42  % (29493)Success in time 0.063 s
%------------------------------------------------------------------------------
