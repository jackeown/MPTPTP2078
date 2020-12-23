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
% DateTime   : Thu Dec  3 13:09:23 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :   12 (  12 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u32,negated_conjecture,(
    ~ m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u31,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u30,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) )).

tff(u29,negated_conjecture,(
    l1_pre_topc(sK0) )).

tff(u28,axiom,(
    ! [X1,X0] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) )).

tff(u27,negated_conjecture,(
    l1_pre_topc(sK1) )).

tff(u26,negated_conjecture,(
    m1_pre_topc(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n025.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 11:30:20 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (23995)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.48  % (24005)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.48  % (24012)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (24002)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.49  % (24002)Refutation not found, incomplete strategy% (24002)------------------------------
% 0.21/0.49  % (24002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (24002)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (24002)Memory used [KB]: 9850
% 0.21/0.49  % (24002)Time elapsed: 0.088 s
% 0.21/0.49  % (24002)------------------------------
% 0.21/0.49  % (24002)------------------------------
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (23995)# SZS output start Saturation.
% 0.21/0.49  tff(u32,negated_conjecture,
% 0.21/0.49      ~m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  tff(u31,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.21/0.49  
% 0.21/0.49  tff(u30,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u29,negated_conjecture,
% 0.21/0.49      l1_pre_topc(sK0)).
% 0.21/0.49  
% 0.21/0.49  tff(u28,axiom,
% 0.21/0.49      (![X1, X0] : ((l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u27,negated_conjecture,
% 0.21/0.49      l1_pre_topc(sK1)).
% 0.21/0.49  
% 0.21/0.49  tff(u26,negated_conjecture,
% 0.21/0.49      m1_pre_topc(sK1,sK0)).
% 0.21/0.49  
% 0.21/0.49  % (23995)# SZS output end Saturation.
% 0.21/0.49  % (23995)------------------------------
% 0.21/0.49  % (23995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (23995)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (23995)Memory used [KB]: 9850
% 0.21/0.49  % (23995)Time elapsed: 0.094 s
% 0.21/0.49  % (23995)------------------------------
% 0.21/0.49  % (23995)------------------------------
% 0.21/0.49  % (23987)Success in time 0.134 s
%------------------------------------------------------------------------------
