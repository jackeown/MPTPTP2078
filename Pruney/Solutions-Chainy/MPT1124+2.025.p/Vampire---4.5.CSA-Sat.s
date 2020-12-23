%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:24 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    0
%              Number of atoms          :   44 (  44 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u85,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u84,negated_conjecture,(
    ~ m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u83,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) )).

tff(u82,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) )).

tff(u81,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u80,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u79,negated_conjecture,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u78,negated_conjecture,(
    v1_xboole_0(u1_struct_0(sK1)) )).

tff(u77,negated_conjecture,(
    ~ r2_hidden(sK2,u1_struct_0(sK0)) )).

tff(u76,negated_conjecture,(
    ~ r2_hidden(sK2,u1_struct_0(sK1)) )).

tff(u75,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) )).

tff(u74,negated_conjecture,(
    ! [X1] :
      ( ~ r2_hidden(X1,u1_struct_0(sK1))
      | m1_subset_1(X1,u1_struct_0(sK0)) ) )).

tff(u73,axiom,(
    ! [X1,X0] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) )).

tff(u72,axiom,(
    ! [X1,X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) )).

tff(u71,negated_conjecture,(
    l1_pre_topc(sK0) )).

tff(u70,negated_conjecture,(
    l1_pre_topc(sK1) )).

tff(u69,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) )).

tff(u68,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u67,negated_conjecture,(
    l1_struct_0(sK1) )).

tff(u66,negated_conjecture,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) )).

tff(u65,negated_conjecture,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | l1_pre_topc(X0) ) )).

tff(u64,axiom,(
    ! [X1,X0] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) )).

tff(u63,negated_conjecture,(
    ! [X0] :
      ( ~ m1_pre_topc(sK0,X0)
      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) )).

tff(u62,negated_conjecture,(
    m1_pre_topc(sK1,sK0) )).

tff(u61,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u60,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (22000)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.45  % (22000)Refutation not found, incomplete strategy% (22000)------------------------------
% 0.20/0.45  % (22000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (22000)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (22000)Memory used [KB]: 6012
% 0.20/0.45  % (22000)Time elapsed: 0.003 s
% 0.20/0.45  % (22000)------------------------------
% 0.20/0.45  % (22000)------------------------------
% 0.20/0.47  % (21995)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.48  % (21995)# SZS output start Saturation.
% 0.20/0.48  tff(u85,axiom,
% 0.20/0.48      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.20/0.48  
% 0.20/0.48  tff(u84,negated_conjecture,
% 0.20/0.48      ~m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.48  
% 0.20/0.48  tff(u83,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u82,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0))))).
% 0.20/0.48  
% 0.20/0.48  tff(u81,negated_conjecture,
% 0.20/0.48      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.20/0.48  
% 0.20/0.48  tff(u80,axiom,
% 0.20/0.48      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.20/0.48  
% 0.20/0.48  tff(u79,negated_conjecture,
% 0.20/0.48      m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.48  
% 0.20/0.48  tff(u78,negated_conjecture,
% 0.20/0.48      v1_xboole_0(u1_struct_0(sK1))).
% 0.20/0.48  
% 0.20/0.48  tff(u77,negated_conjecture,
% 0.20/0.48      ~r2_hidden(sK2,u1_struct_0(sK0))).
% 0.20/0.48  
% 0.20/0.48  tff(u76,negated_conjecture,
% 0.20/0.48      ~r2_hidden(sK2,u1_struct_0(sK1))).
% 0.20/0.48  
% 0.20/0.48  tff(u75,axiom,
% 0.20/0.48      (![X1, X0] : ((~r2_hidden(X0,X1) | m1_subset_1(X0,X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u74,negated_conjecture,
% 0.20/0.48      (![X1] : ((~r2_hidden(X1,u1_struct_0(sK1)) | m1_subset_1(X1,u1_struct_0(sK0)))))).
% 0.20/0.48  
% 0.20/0.48  tff(u73,axiom,
% 0.20/0.48      (![X1, X0] : ((r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u72,axiom,
% 0.20/0.48      (![X1, X0] : ((~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u71,negated_conjecture,
% 0.20/0.48      l1_pre_topc(sK0)).
% 0.20/0.48  
% 0.20/0.48  tff(u70,negated_conjecture,
% 0.20/0.48      l1_pre_topc(sK1)).
% 0.20/0.48  
% 0.20/0.48  tff(u69,axiom,
% 0.20/0.48      (![X0] : ((l1_struct_0(X0) | ~l1_pre_topc(X0))))).
% 0.20/0.48  
% 0.20/0.48  tff(u68,negated_conjecture,
% 0.20/0.48      l1_struct_0(sK0)).
% 0.20/0.48  
% 0.20/0.48  tff(u67,negated_conjecture,
% 0.20/0.48      l1_struct_0(sK1)).
% 0.20/0.48  
% 0.20/0.48  tff(u66,negated_conjecture,
% 0.20/0.48      (![X0] : ((~m1_pre_topc(X0,sK0) | l1_pre_topc(X0))))).
% 0.20/0.48  
% 0.20/0.48  tff(u65,negated_conjecture,
% 0.20/0.48      (![X0] : ((~m1_pre_topc(X0,sK1) | l1_pre_topc(X0))))).
% 0.20/0.48  
% 0.20/0.48  tff(u64,axiom,
% 0.20/0.48      (![X1, X0] : ((~m1_pre_topc(X0,X1) | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1))))).
% 0.20/0.48  
% 0.20/0.48  tff(u63,negated_conjecture,
% 0.20/0.48      (![X0] : ((~m1_pre_topc(sK0,X0) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))))).
% 0.20/0.48  
% 0.20/0.48  tff(u62,negated_conjecture,
% 0.20/0.48      m1_pre_topc(sK1,sK0)).
% 0.20/0.48  
% 0.20/0.48  tff(u61,negated_conjecture,
% 0.20/0.48      ~v2_struct_0(sK0)).
% 0.20/0.48  
% 0.20/0.48  tff(u60,negated_conjecture,
% 0.20/0.48      ~v2_struct_0(sK1)).
% 0.20/0.48  
% 0.20/0.48  % (21995)# SZS output end Saturation.
% 0.20/0.48  % (21995)------------------------------
% 0.20/0.48  % (21995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (21995)Termination reason: Satisfiable
% 0.20/0.48  
% 0.20/0.48  % (21995)Memory used [KB]: 10618
% 0.20/0.48  % (21995)Time elapsed: 0.048 s
% 0.20/0.48  % (21995)------------------------------
% 0.20/0.48  % (21995)------------------------------
% 0.20/0.48  % (21978)Success in time 0.122 s
%------------------------------------------------------------------------------
