%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:15 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    0
%              Number of atoms          :  140 ( 140 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   15 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u181,negated_conjecture,
    ( ~ v15_waybel_0(sK1,sK0)
    | ! [X2] :
        ( k6_waybel_0(sK0,X2) != sK1
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) )).

tff(u180,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) )).

tff(u179,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u178,negated_conjecture,
    ( ~ ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u177,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | r3_orders_2(sK0,X0,X1) ) )).

tff(u176,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u175,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u174,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | ! [X1,X0,X2] :
        ( m1_subset_1(sK3(sK0,X1,X0),X2)
        | r1_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u173,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK4(X0,X1,X2),X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) )).

tff(u172,axiom,(
    ! [X1,X3,X0,X2] :
      ( m1_subset_1(sK4(X2,X0,X1),X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
      | r1_tarski(X0,X1) ) )).

tff(u171,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) )).

tff(u170,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) )).

tff(u169,negated_conjecture,
    ( ~ ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK2,sK1) )).

tff(u168,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) )).

tff(u167,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | ! [X1,X0] :
        ( r2_hidden(sK3(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1) ) )).

tff(u166,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u165,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | v3_orders_2(sK0) )).

tff(u164,axiom,(
    ! [X1,X0,X2] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u163,axiom,(
    ! [X1,X0,X2] :
      ( ~ l1_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u162,axiom,(
    ! [X1,X0,X2] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) )).

tff(u161,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u160,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ! [X1,X0] :
        ( ~ r3_orders_2(sK0,X1,sK3(sK0,X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1) ) )).

tff(u159,axiom,(
    ! [X1,X0] :
      ( r3_orders_2(X1,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) )).

tff(u158,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u157,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK0,sK3(sK0,X1,X2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,sK3(sK0,X1,X2),X0)
        | r1_lattice3(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) )).

tff(u156,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_orders_2(sK0,sK4(u1_struct_0(sK0),X4,X5),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r3_orders_2(sK0,sK4(u1_struct_0(sK0),X4,X5),X3)
        | r1_tarski(X4,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) )).

tff(u155,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ! [X1,X3,X0,X2] :
        ( ~ r1_orders_2(sK0,sK4(X1,X2,X0),X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X2,X0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r3_orders_2(sK0,sK4(X1,X2,X0),X3) ) )).

tff(u154,axiom,(
    ! [X1,X0] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u153,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ! [X1,X0] :
        ( r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_orders_2(sK0,X0,X1) ) )).

tff(u152,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u151,negated_conjecture,
    ( ~ v15_waybel_0(sK1,sK0)
    | v15_waybel_0(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:53:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (27945)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.47  % (27937)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.48  % (27937)Refutation not found, incomplete strategy% (27937)------------------------------
% 0.21/0.48  % (27937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (27937)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (27937)Memory used [KB]: 6140
% 0.21/0.48  % (27937)Time elapsed: 0.064 s
% 0.21/0.48  % (27937)------------------------------
% 0.21/0.48  % (27937)------------------------------
% 0.21/0.48  % (27945)# SZS output start Saturation.
% 0.21/0.48  tff(u181,negated_conjecture,
% 0.21/0.48      ((~v15_waybel_0(sK1,sK0)) | (![X2] : (((k6_waybel_0(sK0,X2) != sK1) | ~m1_subset_1(X2,u1_struct_0(sK0))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u180,axiom,
% 0.21/0.48      (![X1, X0] : ((~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | (X0 = X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u179,axiom,
% 0.21/0.48      (![X1] : (r1_tarski(X1,X1)))).
% 0.21/0.48  
% 0.21/0.48  tff(u178,negated_conjecture,
% 0.21/0.48      ((~~m1_subset_1(sK2,u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u177,negated_conjecture,
% 0.21/0.48      ((~~v2_struct_0(sK0)) | (~v3_orders_2(sK0)) | (~l1_orders_2(sK0)) | (![X1, X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | r3_orders_2(sK0,X0,X1)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u176,negated_conjecture,
% 0.21/0.48      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u175,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u174,negated_conjecture,
% 0.21/0.48      ((~l1_orders_2(sK0)) | (![X1, X0, X2] : ((m1_subset_1(sK3(sK0,X1,X0),X2) | r1_lattice3(sK0,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,u1_struct_0(sK0))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u173,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((m1_subset_1(sK4(X0,X1,X2),X0) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u172,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((m1_subset_1(sK4(X2,X0,X1),X3) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(X3)) | r1_tarski(X0,X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u171,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u170,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~r2_hidden(sK4(X0,X1,X2),X2) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u169,negated_conjecture,
% 0.21/0.48      ((~~r2_hidden(sK2,sK1)) | ~r2_hidden(sK2,sK1))).
% 0.21/0.48  
% 0.21/0.48  tff(u168,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((r2_hidden(sK4(X0,X1,X2),X1) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u167,negated_conjecture,
% 0.21/0.48      ((~l1_orders_2(sK0)) | (![X1, X0] : ((r2_hidden(sK3(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u166,negated_conjecture,
% 0.21/0.48      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.21/0.48  
% 0.21/0.48  tff(u165,negated_conjecture,
% 0.21/0.48      ((~v3_orders_2(sK0)) | v3_orders_2(sK0))).
% 0.21/0.48  
% 0.21/0.48  tff(u164,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u163,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~l1_orders_2(X0) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u162,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~l1_orders_2(X0) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u161,negated_conjecture,
% 0.21/0.48      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.21/0.48  
% 0.21/0.48  tff(u160,negated_conjecture,
% 0.21/0.48      ((~~v2_struct_0(sK0)) | (~v3_orders_2(sK0)) | (~l1_orders_2(sK0)) | (![X1, X0] : ((~r3_orders_2(sK0,X1,sK3(sK0,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u159,axiom,
% 0.21/0.48      (![X1, X0] : ((r3_orders_2(X1,X0,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u158,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u157,negated_conjecture,
% 0.21/0.48      ((~~v2_struct_0(sK0)) | (~v3_orders_2(sK0)) | (~l1_orders_2(sK0)) | (![X1, X0, X2] : ((~r1_orders_2(sK0,sK3(sK0,X1,X2),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,sK3(sK0,X1,X2),X0) | r1_lattice3(sK0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u156,negated_conjecture,
% 0.21/0.48      ((~~v2_struct_0(sK0)) | (~v3_orders_2(sK0)) | (~l1_orders_2(sK0)) | (![X3, X5, X4] : ((~r1_orders_2(sK0,sK4(u1_struct_0(sK0),X4,X5),X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r3_orders_2(sK0,sK4(u1_struct_0(sK0),X4,X5),X3) | r1_tarski(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u155,negated_conjecture,
% 0.21/0.48      ((~~v2_struct_0(sK0)) | (~v3_orders_2(sK0)) | (~l1_orders_2(sK0)) | (![X1, X3, X0, X2] : ((~r1_orders_2(sK0,sK4(X1,X2,X0),X3) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X2,X0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r3_orders_2(sK0,sK4(X1,X2,X0),X3)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u154,axiom,
% 0.21/0.48      (![X1, X0] : ((r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u153,negated_conjecture,
% 0.21/0.48      ((~~v2_struct_0(sK0)) | (~v3_orders_2(sK0)) | (~l1_orders_2(sK0)) | (![X1, X0] : ((r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_orders_2(sK0,X0,X1)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u152,axiom,
% 0.21/0.48      (![X1, X0, X2, X4] : ((~r1_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X2,X4) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u151,negated_conjecture,
% 0.21/0.48      ((~v15_waybel_0(sK1,sK0)) | v15_waybel_0(sK1,sK0))).
% 0.21/0.48  
% 0.21/0.48  % (27945)# SZS output end Saturation.
% 0.21/0.48  % (27945)------------------------------
% 0.21/0.48  % (27945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (27945)Termination reason: Satisfiable
% 0.21/0.48  
% 0.21/0.48  % (27945)Memory used [KB]: 10746
% 0.21/0.48  % (27945)Time elapsed: 0.068 s
% 0.21/0.48  % (27945)------------------------------
% 0.21/0.48  % (27945)------------------------------
% 0.21/0.48  % (27921)Success in time 0.125 s
%------------------------------------------------------------------------------
