%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:52 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    0
%              Number of atoms          :   84 (  84 expanded)
%              Number of equality atoms :   28 (  28 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u186,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ! [X3,X2] :
        ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK0) = X2 ) )).

tff(u185,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(sK0) = X1 ) )).

tff(u184,negated_conjecture,
    ( u1_orders_2(sK0) != u1_orders_2(sK1)
    | u1_orders_2(sK0) = u1_orders_2(sK1) )).

tff(u183,negated_conjecture,
    ( u1_struct_0(sK0) != u1_struct_0(sK1)
    | u1_struct_0(sK0) = u1_struct_0(sK1) )).

tff(u182,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) )).

tff(u181,negated_conjecture,
    ( sK2 != sK3
    | sK2 = sK3 )).

tff(u180,axiom,(
    ! [X1,X0,X2] :
      ( ~ l1_orders_2(X0)
      | u1_orders_2(X0) = X2
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) ) )).

tff(u179,axiom,(
    ! [X1,X0,X2] :
      ( ~ l1_orders_2(X0)
      | u1_struct_0(X0) = X1
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) ) )).

tff(u178,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u177,negated_conjecture,
    ( ~ l1_orders_2(sK1)
    | l1_orders_2(sK1) )).

tff(u176,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) )).

tff(u175,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) )).

tff(u174,axiom,(
    ! [X1,X5,X0,X4] :
      ( ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | r1_orders_2(X1,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) )).

tff(u173,axiom,(
    ! [X1,X5,X0,X4] :
      ( ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_orders_2(X0,X4,X5)
      | r2_orders_2(X1,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) )).

tff(u172,negated_conjecture,
    ( ~ l1_orders_2(sK1)
    | u1_orders_2(sK0) != u1_orders_2(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK1)
    | ! [X3,X5,X4] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_orders_2(X4,X5,X3)
        | r2_orders_2(sK1,X5,X3)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
        | ~ m1_subset_1(X3,u1_struct_0(X4))
        | ~ m1_subset_1(X5,u1_struct_0(X4))
        | ~ l1_orders_2(X4) ) )).

tff(u171,negated_conjecture,
    ( ~ l1_orders_2(sK1)
    | u1_orders_2(sK0) != u1_orders_2(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK1)
    | ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(X1,X2,X0)
        | r1_orders_2(sK1,X2,X0)
        | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ l1_orders_2(X1) ) )).

tff(u170,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u169,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) )).

tff(u168,axiom,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) )).

tff(u167,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u166,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) )).

tff(u165,negated_conjecture,
    ( ~ ~ v1_waybel_0(sK2,sK1)
    | ~ v1_waybel_0(sK2,sK1) )).

tff(u164,negated_conjecture,
    ( ~ v1_waybel_0(sK2,sK0)
    | v1_waybel_0(sK2,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:30:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (32566)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.46  % (32550)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.47  % (32550)Refutation not found, incomplete strategy% (32550)------------------------------
% 0.21/0.47  % (32550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (32550)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (32550)Memory used [KB]: 1663
% 0.21/0.47  % (32550)Time elapsed: 0.057 s
% 0.21/0.47  % (32550)------------------------------
% 0.21/0.47  % (32550)------------------------------
% 0.21/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.47  % (32566)# SZS output start Saturation.
% 0.21/0.47  tff(u186,negated_conjecture,
% 0.21/0.47      ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | (![X3, X2] : (((g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | (u1_struct_0(sK0) = X2)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u185,negated_conjecture,
% 0.21/0.47      ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | (![X1, X0] : (((g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | (u1_orders_2(sK0) = X1)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u184,negated_conjecture,
% 0.21/0.47      ((~(u1_orders_2(sK0) = u1_orders_2(sK1))) | (u1_orders_2(sK0) = u1_orders_2(sK1)))).
% 0.21/0.47  
% 0.21/0.47  tff(u183,negated_conjecture,
% 0.21/0.47      ((~(u1_struct_0(sK0) = u1_struct_0(sK1))) | (u1_struct_0(sK0) = u1_struct_0(sK1)))).
% 0.21/0.47  
% 0.21/0.47  tff(u182,negated_conjecture,
% 0.21/0.47      ((~(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)))) | (g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))))).
% 0.21/0.47  
% 0.21/0.47  tff(u181,negated_conjecture,
% 0.21/0.47      ((~(sK2 = sK3)) | (sK2 = sK3))).
% 0.21/0.47  
% 0.21/0.47  tff(u180,axiom,
% 0.21/0.47      (![X1, X0, X2] : ((~l1_orders_2(X0) | (u1_orders_2(X0) = X2) | (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u179,axiom,
% 0.21/0.47      (![X1, X0, X2] : ((~l1_orders_2(X0) | (u1_struct_0(X0) = X1) | (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u178,negated_conjecture,
% 0.21/0.47      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.21/0.47  
% 0.21/0.47  tff(u177,negated_conjecture,
% 0.21/0.47      ((~l1_orders_2(sK1)) | l1_orders_2(sK1))).
% 0.21/0.47  
% 0.21/0.47  tff(u176,axiom,
% 0.21/0.47      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X1 = X3))))).
% 0.21/0.47  
% 0.21/0.47  tff(u175,axiom,
% 0.21/0.47      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X0 = X2))))).
% 0.21/0.47  
% 0.21/0.47  tff(u174,axiom,
% 0.21/0.47      (![X1, X5, X0, X4] : ((~m1_subset_1(X5,u1_struct_0(X1)) | ~r1_orders_2(X0,X4,X5) | r1_orders_2(X1,X4,X5) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) | ~l1_orders_2(X1) | ~l1_orders_2(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u173,axiom,
% 0.21/0.47      (![X1, X5, X0, X4] : ((~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_orders_2(X0,X4,X5) | r2_orders_2(X1,X4,X5) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) | ~l1_orders_2(X1) | ~l1_orders_2(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u172,negated_conjecture,
% 0.21/0.47      ((~l1_orders_2(sK1)) | (~(u1_orders_2(sK0) = u1_orders_2(sK1))) | (~(u1_struct_0(sK0) = u1_struct_0(sK1))) | (![X3, X5, X4] : ((~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_orders_2(X4,X5,X3) | r2_orders_2(sK1,X5,X3) | (g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))) | ~m1_subset_1(X3,u1_struct_0(X4)) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l1_orders_2(X4)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u171,negated_conjecture,
% 0.21/0.47      ((~l1_orders_2(sK1)) | (~(u1_orders_2(sK0) = u1_orders_2(sK1))) | (~(u1_struct_0(sK0) = u1_struct_0(sK1))) | (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(X1,X2,X0) | r1_orders_2(sK1,X2,X0) | (g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u170,negated_conjecture,
% 0.21/0.47      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u169,negated_conjecture,
% 0.21/0.47      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))))).
% 0.21/0.47  
% 0.21/0.47  tff(u168,axiom,
% 0.21/0.47      (![X0] : ((m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u167,negated_conjecture,
% 0.21/0.47      ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u166,negated_conjecture,
% 0.21/0.47      ((~m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))) | m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u165,negated_conjecture,
% 0.21/0.47      ((~~v1_waybel_0(sK2,sK1)) | ~v1_waybel_0(sK2,sK1))).
% 0.21/0.47  
% 0.21/0.47  tff(u164,negated_conjecture,
% 0.21/0.47      ((~v1_waybel_0(sK2,sK0)) | v1_waybel_0(sK2,sK0))).
% 0.21/0.47  
% 0.21/0.47  % (32566)# SZS output end Saturation.
% 0.21/0.47  % (32566)------------------------------
% 0.21/0.47  % (32566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (32566)Termination reason: Satisfiable
% 0.21/0.47  
% 0.21/0.47  % (32566)Memory used [KB]: 10746
% 0.21/0.47  % (32566)Time elapsed: 0.070 s
% 0.21/0.47  % (32566)------------------------------
% 0.21/0.47  % (32566)------------------------------
% 0.21/0.47  % (32542)Success in time 0.113 s
%------------------------------------------------------------------------------
