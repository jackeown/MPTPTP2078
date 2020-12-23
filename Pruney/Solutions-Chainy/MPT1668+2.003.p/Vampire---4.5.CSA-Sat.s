%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:14 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    0
%              Number of atoms          :  105 ( 105 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u175,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ ! [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK0))
          | sK1 != k5_waybel_0(sK0,X2) )
    | ! [X0] :
        ( sK1 != k5_waybel_0(sK0,sK4(sK1,X0))
        | r1_tarski(sK1,X0) ) )).

% (10321)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
tff(u174,negated_conjecture,
    ( sK1 != k5_waybel_0(sK0,sK2)
    | sK1 = k5_waybel_0(sK0,sK2) )).

tff(u173,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK4(X0,X1),X2)
      | r1_tarski(X0,X1) ) )).

tff(u172,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) )).

tff(u171,negated_conjecture,
    ( ~ ! [X6] : r1_tarski(sK1,X6)
    | ! [X2] :
        ( ~ r1_tarski(X2,sK1)
        | sK1 = X2 ) )).

tff(u170,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ ! [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK0))
          | sK1 != k5_waybel_0(sK0,X2) )
    | ! [X0] :
        ( ~ r1_tarski(k5_waybel_0(sK0,sK4(sK1,X0)),sK1)
        | ~ r1_tarski(sK1,k5_waybel_0(sK0,sK4(sK1,X0)))
        | r1_tarski(sK1,X0) ) )).

tff(u169,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u168,negated_conjecture,
    ( ~ ! [X6] : r1_tarski(sK1,X6)
    | ! [X6] : r1_tarski(sK1,X6) )).

tff(u167,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) )).

tff(u166,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) )).

tff(u165,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) )).

tff(u164,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) )).

tff(u163,negated_conjecture,
    ( ~ ! [X5,X4] :
          ( r2_hidden(sK3(sK0,X5,sK4(sK1,X4)),X5)
          | r2_lattice3(sK0,X5,sK4(sK1,X4))
          | r1_tarski(sK1,X4) )
    | ! [X5,X4] :
        ( r2_hidden(sK3(sK0,X5,sK4(sK1,X4)),X5)
        | r2_lattice3(sK0,X5,sK4(sK1,X4))
        | r1_tarski(sK1,X4) ) )).

tff(u162,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) )).

tff(u161,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) )).

tff(u160,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r3_orders_2(X0,X1,X1)
      | ~ sP5(X0) ) )).

tff(u159,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) )).

tff(u158,axiom,(
    ! [X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP5(X0) ) )).

tff(u157,negated_conjecture,
    ( ~ ! [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK0))
          | sK1 != k5_waybel_0(sK0,X2) )
    | ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK1 != k5_waybel_0(sK0,X2) ) )).

tff(u156,negated_conjecture,
    ( ~ ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u155,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK4(X0,X2),X1)
      | r1_tarski(X0,X2) ) )).

tff(u154,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u153,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] :
        ( m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
        | r1_tarski(sK1,X0) ) )).

tff(u152,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u151,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | v3_orders_2(sK0) )).

tff(u150,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u149,axiom,(
    ! [X1,X0,X2] :
      ( ~ r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) )).

tff(u148,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) )).

tff(u147,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_orders_2(X0,X1,X2) ) )).

tff(u146,negated_conjecture,
    ( ~ v14_waybel_0(sK1,sK0)
    | v14_waybel_0(sK1,sK0) )).

tff(u145,negated_conjecture,
    ( ~ ~ sP5(sK0)
    | ~ sP5(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:03:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (10316)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (10324)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (10316)Refutation not found, incomplete strategy% (10316)------------------------------
% 0.20/0.52  % (10316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10316)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10316)Memory used [KB]: 1663
% 0.20/0.52  % (10316)Time elapsed: 0.103 s
% 0.20/0.52  % (10316)------------------------------
% 0.20/0.52  % (10316)------------------------------
% 0.20/0.52  % (10319)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (10332)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (10331)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.53  % (10332)# SZS output start Saturation.
% 0.20/0.53  tff(u175,negated_conjecture,
% 0.20/0.53      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (~(![X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | (sK1 != k5_waybel_0(sK0,X2)))))) | (![X0] : (((sK1 != k5_waybel_0(sK0,sK4(sK1,X0))) | r1_tarski(sK1,X0)))))).
% 0.20/0.53  
% 0.20/0.53  % (10321)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  tff(u174,negated_conjecture,
% 0.20/0.53      ((~(sK1 = k5_waybel_0(sK0,sK2))) | (sK1 = k5_waybel_0(sK0,sK2)))).
% 0.20/0.53  
% 0.20/0.53  tff(u173,axiom,
% 0.20/0.53      (![X1, X0, X2] : ((~r1_tarski(X0,X2) | r2_hidden(sK4(X0,X1),X2) | r1_tarski(X0,X1))))).
% 0.20/0.53  
% 0.20/0.53  tff(u172,axiom,
% 0.20/0.53      (![X1, X0] : ((~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | (X0 = X1))))).
% 0.20/0.53  
% 0.20/0.53  tff(u171,negated_conjecture,
% 0.20/0.53      ((~(![X6] : (r1_tarski(sK1,X6)))) | (![X2] : ((~r1_tarski(X2,sK1) | (sK1 = X2)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u170,negated_conjecture,
% 0.20/0.53      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (~(![X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | (sK1 != k5_waybel_0(sK0,X2)))))) | (![X0] : ((~r1_tarski(k5_waybel_0(sK0,sK4(sK1,X0)),sK1) | ~r1_tarski(sK1,k5_waybel_0(sK0,sK4(sK1,X0))) | r1_tarski(sK1,X0)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u169,axiom,
% 0.20/0.53      (![X1] : (r1_tarski(X1,X1)))).
% 0.20/0.53  
% 0.20/0.53  tff(u168,negated_conjecture,
% 0.20/0.53      ((~(![X6] : (r1_tarski(sK1,X6)))) | (![X6] : (r1_tarski(sK1,X6))))).
% 0.20/0.53  
% 0.20/0.53  tff(u167,axiom,
% 0.20/0.53      (![X1, X0] : ((~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1))))).
% 0.20/0.53  
% 0.20/0.53  tff(u166,axiom,
% 0.20/0.53      (![X1, X0, X2] : ((~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))))).
% 0.20/0.53  
% 0.20/0.53  tff(u165,axiom,
% 0.20/0.53      (![X1, X0, X2] : ((~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1))))).
% 0.20/0.53  
% 0.20/0.53  tff(u164,axiom,
% 0.20/0.53      (![X1, X0] : ((r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1))))).
% 0.20/0.53  
% 0.20/0.53  tff(u163,negated_conjecture,
% 0.20/0.53      ((~(![X5, X4] : ((r2_hidden(sK3(sK0,X5,sK4(sK1,X4)),X5) | r2_lattice3(sK0,X5,sK4(sK1,X4)) | r1_tarski(sK1,X4))))) | (![X5, X4] : ((r2_hidden(sK3(sK0,X5,sK4(sK1,X4)),X5) | r2_lattice3(sK0,X5,sK4(sK1,X4)) | r1_tarski(sK1,X4)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u162,axiom,
% 0.20/0.53      (![X1, X3, X0, X2] : ((~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X3,X2) | ~r2_lattice3(X0,X1,X2))))).
% 0.20/0.53  
% 0.20/0.53  tff(u161,axiom,
% 0.20/0.53      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2))))).
% 0.20/0.53  
% 0.20/0.53  tff(u160,axiom,
% 0.20/0.53      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r3_orders_2(X0,X1,X1) | ~sP5(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u159,axiom,
% 0.20/0.53      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(sK3(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2))))).
% 0.20/0.53  
% 0.20/0.53  tff(u158,axiom,
% 0.20/0.53      (![X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP5(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u157,negated_conjecture,
% 0.20/0.53      ((~(![X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | (sK1 != k5_waybel_0(sK0,X2)))))) | (![X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | (sK1 != k5_waybel_0(sK0,X2))))))).
% 0.20/0.53  
% 0.20/0.53  tff(u156,negated_conjecture,
% 0.20/0.53      ((~~m1_subset_1(sK2,u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)))).
% 0.20/0.53  
% 0.20/0.53  tff(u155,axiom,
% 0.20/0.53      (![X1, X0, X2] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK4(X0,X2),X1) | r1_tarski(X0,X2))))).
% 0.20/0.53  
% 0.20/0.53  tff(u154,negated_conjecture,
% 0.20/0.53      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u153,negated_conjecture,
% 0.20/0.53      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0)) | r1_tarski(sK1,X0)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u152,negated_conjecture,
% 0.20/0.53      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  tff(u151,negated_conjecture,
% 0.20/0.53      ((~v3_orders_2(sK0)) | v3_orders_2(sK0))).
% 0.20/0.53  
% 0.20/0.53  tff(u150,negated_conjecture,
% 0.20/0.53      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.20/0.53  
% 0.20/0.53  tff(u149,axiom,
% 0.20/0.53      (![X1, X0, X2] : ((~r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | v2_struct_0(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u148,axiom,
% 0.20/0.53      (![X1, X0, X2] : ((~r1_orders_2(X0,sK3(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2))))).
% 0.20/0.53  
% 0.20/0.53  tff(u147,axiom,
% 0.20/0.53      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r3_orders_2(X0,X1,X2))))).
% 0.20/0.53  
% 0.20/0.53  tff(u146,negated_conjecture,
% 0.20/0.53      ((~v14_waybel_0(sK1,sK0)) | v14_waybel_0(sK1,sK0))).
% 0.20/0.53  
% 0.20/0.53  tff(u145,negated_conjecture,
% 0.20/0.53      ((~~sP5(sK0)) | ~sP5(sK0))).
% 0.20/0.53  
% 0.20/0.53  % (10332)# SZS output end Saturation.
% 0.20/0.53  % (10332)------------------------------
% 0.20/0.53  % (10332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (10332)Termination reason: Satisfiable
% 0.20/0.53  
% 0.20/0.53  % (10332)Memory used [KB]: 10746
% 0.20/0.53  % (10332)Time elapsed: 0.111 s
% 0.20/0.53  % (10332)------------------------------
% 0.20/0.53  % (10332)------------------------------
% 0.20/0.53  % (10315)Success in time 0.164 s
%------------------------------------------------------------------------------
