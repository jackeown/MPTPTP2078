%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:01 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  34 expanded)
%              Number of leaves         :   34 (  34 expanded)
%              Depth                    :    0
%              Number of atoms          :   83 (  83 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (19425)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
tff(u109,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

% (19418)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
tff(u108,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | sP2(X2,X1,X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) )).

tff(u107,negated_conjecture,(
    m1_subset_1(sK4,u1_struct_0(sK3)) )).

tff(u106,negated_conjecture,(
    m1_subset_1(sK5,u1_struct_0(sK3)) )).

tff(u105,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u104,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK7(X0,X1,X2),X2)
      | ~ sP2(X0,X1,X2) ) )).

tff(u103,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(sK7(X0,X1,X2),X0)
      | ~ sP2(X0,X1,X2) ) )).

tff(u102,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u101,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK7(X0,X1,X2),X1)
      | ~ sP2(X0,X1,X2) ) )).

tff(u100,negated_conjecture,(
    ~ r1_tarski(k5_waybel_0(sK3,sK4),k5_waybel_0(sK3,sK5)) )).

tff(u99,axiom,(
    ! [X1,X0,X2] :
      ( r1_tarski(sK7(X0,X1,k1_zfmisc_1(X2)),sK7(X0,X1,k1_zfmisc_1(X2)))
      | ~ sP2(X0,X1,k1_zfmisc_1(X2)) ) )).

tff(u98,negated_conjecture,(
    l1_orders_2(sK3) )).

tff(u97,negated_conjecture,(
    ! [X0] :
      ( ~ r2_lattice3(sK3,X0,sK4)
      | r2_lattice3(sK3,X0,sK5) ) )).

tff(u96,negated_conjecture,(
    ! [X0] :
      ( ~ r2_lattice3(sK3,X0,sK4)
      | sP0(sK4,sK3,X0) ) )).

tff(u95,negated_conjecture,(
    ! [X1] :
      ( ~ r2_lattice3(sK3,X1,sK5)
      | sP0(sK5,sK3,X1) ) )).

tff(u94,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X5,X7,sK6(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK6(X4,X5,X6),X5,X7) ) )).

tff(u93,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X6,X7,sK7(X4,X5,u1_struct_0(X6)))
      | ~ l1_orders_2(X6)
      | ~ sP2(X4,X5,u1_struct_0(X6))
      | sP0(sK7(X4,X5,u1_struct_0(X6)),X6,X7) ) )).

tff(u92,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,sK6(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) )).

tff(u91,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X2,X3)
      | r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u90,negated_conjecture,(
    r1_orders_2(sK3,sK4,sK5) )).

tff(u89,negated_conjecture,(
    v4_orders_2(sK3) )).

tff(u88,negated_conjecture,(
    ! [X0] :
      ( ~ sP0(sK4,sK3,X0)
      | r2_lattice3(sK3,X0,sK4) ) )).

tff(u87,negated_conjecture,(
    ! [X1] :
      ( ~ sP0(sK5,sK3,X1)
      | r2_lattice3(sK3,X1,sK5) ) )).

tff(u86,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X0) ) )).

tff(u85,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK6(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r2_lattice3(X1,X3,sK6(X0,X1,X2)) ) )).

tff(u84,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK7(X0,X1,u1_struct_0(X2)),X2,X3)
      | ~ l1_orders_2(X2)
      | ~ sP2(X0,X1,u1_struct_0(X2))
      | r2_lattice3(X2,X3,sK7(X0,X1,u1_struct_0(X2))) ) )).

tff(u83,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_lattice3(X1,X0,X2) ) )).

tff(u82,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u81,negated_conjecture,(
    ! [X0] : sP1(X0,sK3,sK4) )).

tff(u80,negated_conjecture,(
    ! [X1] : sP1(X1,sK3,sK5) )).

tff(u79,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP1(X3,X1,sK6(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

tff(u78,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP1(X3,X2,sK7(X0,X1,u1_struct_0(X2)))
      | ~ sP2(X0,X1,u1_struct_0(X2))
      | ~ l1_orders_2(X2) ) )).

tff(u77,axiom,(
    ! [X1,X0] : ~ sP2(X0,X0,X1) )).

tff(u76,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP2(sK7(X0,X1,k1_zfmisc_1(X2)),X3,X2)
      | r1_tarski(X3,sK7(X0,X1,k1_zfmisc_1(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ sP2(X0,X1,k1_zfmisc_1(X2)) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:06:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (19431)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (19421)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (19427)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.49  % (19420)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (19420)# SZS output start Saturation.
% 0.21/0.49  % (19425)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.49  tff(u109,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  % (19418)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.49  tff(u108,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X0)) | sP2(X2,X1,X0) | r1_tarski(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u107,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK4,u1_struct_0(sK3))).
% 0.21/0.49  
% 0.21/0.49  tff(u106,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK5,u1_struct_0(sK3))).
% 0.21/0.49  
% 0.21/0.49  tff(u105,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u104,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((m1_subset_1(sK7(X0,X1,X2),X2) | ~sP2(X0,X1,X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u103,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~r2_hidden(sK7(X0,X1,X2),X0) | ~sP2(X0,X1,X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u102,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((r2_hidden(sK6(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u101,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((r2_hidden(sK7(X0,X1,X2),X1) | ~sP2(X0,X1,X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u100,negated_conjecture,
% 0.21/0.49      ~r1_tarski(k5_waybel_0(sK3,sK4),k5_waybel_0(sK3,sK5))).
% 0.21/0.49  
% 0.21/0.49  tff(u99,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((r1_tarski(sK7(X0,X1,k1_zfmisc_1(X2)),sK7(X0,X1,k1_zfmisc_1(X2))) | ~sP2(X0,X1,k1_zfmisc_1(X2)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u98,negated_conjecture,
% 0.21/0.49      l1_orders_2(sK3)).
% 0.21/0.49  
% 0.21/0.49  tff(u97,negated_conjecture,
% 0.21/0.49      (![X0] : ((~r2_lattice3(sK3,X0,sK4) | r2_lattice3(sK3,X0,sK5))))).
% 0.21/0.49  
% 0.21/0.49  tff(u96,negated_conjecture,
% 0.21/0.49      (![X0] : ((~r2_lattice3(sK3,X0,sK4) | sP0(sK4,sK3,X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u95,negated_conjecture,
% 0.21/0.49      (![X1] : ((~r2_lattice3(sK3,X1,sK5) | sP0(sK5,sK3,X1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u94,axiom,
% 0.21/0.49      (![X5, X7, X4, X6] : ((~r2_lattice3(X5,X7,sK6(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK6(X4,X5,X6),X5,X7))))).
% 0.21/0.49  
% 0.21/0.49  tff(u93,axiom,
% 0.21/0.49      (![X5, X7, X4, X6] : ((~r2_lattice3(X6,X7,sK7(X4,X5,u1_struct_0(X6))) | ~l1_orders_2(X6) | ~sP2(X4,X5,u1_struct_0(X6)) | sP0(sK7(X4,X5,u1_struct_0(X6)),X6,X7))))).
% 0.21/0.49  
% 0.21/0.49  tff(u92,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~r1_orders_2(X1,sK6(X0,X1,X2),X0) | sP0(X0,X1,X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u91,axiom,
% 0.21/0.49      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X2,X3) | r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u90,negated_conjecture,
% 0.21/0.49      r1_orders_2(sK3,sK4,sK5)).
% 0.21/0.49  
% 0.21/0.49  tff(u89,negated_conjecture,
% 0.21/0.49      v4_orders_2(sK3)).
% 0.21/0.49  
% 0.21/0.49  tff(u88,negated_conjecture,
% 0.21/0.49      (![X0] : ((~sP0(sK4,sK3,X0) | r2_lattice3(sK3,X0,sK4))))).
% 0.21/0.49  
% 0.21/0.49  tff(u87,negated_conjecture,
% 0.21/0.49      (![X1] : ((~sP0(sK5,sK3,X1) | r2_lattice3(sK3,X1,sK5))))).
% 0.21/0.49  
% 0.21/0.49  tff(u86,axiom,
% 0.21/0.49      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u85,axiom,
% 0.21/0.49      (![X1, X3, X0, X2] : ((~sP0(sK6(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r2_lattice3(X1,X3,sK6(X0,X1,X2)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u84,axiom,
% 0.21/0.49      (![X1, X3, X0, X2] : ((~sP0(sK7(X0,X1,u1_struct_0(X2)),X2,X3) | ~l1_orders_2(X2) | ~sP2(X0,X1,u1_struct_0(X2)) | r2_lattice3(X2,X3,sK7(X0,X1,u1_struct_0(X2))))))).
% 0.21/0.49  
% 0.21/0.49  tff(u83,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_lattice3(X1,X0,X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u82,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r2_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u81,negated_conjecture,
% 0.21/0.49      (![X0] : (sP1(X0,sK3,sK4)))).
% 0.21/0.49  
% 0.21/0.49  tff(u80,negated_conjecture,
% 0.21/0.49      (![X1] : (sP1(X1,sK3,sK5)))).
% 0.21/0.49  
% 0.21/0.49  tff(u79,axiom,
% 0.21/0.49      (![X1, X3, X0, X2] : ((sP1(X3,X1,sK6(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u78,axiom,
% 0.21/0.49      (![X1, X3, X0, X2] : ((sP1(X3,X2,sK7(X0,X1,u1_struct_0(X2))) | ~sP2(X0,X1,u1_struct_0(X2)) | ~l1_orders_2(X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u77,axiom,
% 0.21/0.49      (![X1, X0] : (~sP2(X0,X0,X1)))).
% 0.21/0.49  
% 0.21/0.49  tff(u76,axiom,
% 0.21/0.49      (![X1, X3, X0, X2] : ((sP2(sK7(X0,X1,k1_zfmisc_1(X2)),X3,X2) | r1_tarski(X3,sK7(X0,X1,k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~sP2(X0,X1,k1_zfmisc_1(X2)))))).
% 0.21/0.49  
% 0.21/0.49  % (19420)# SZS output end Saturation.
% 0.21/0.49  % (19420)------------------------------
% 0.21/0.49  % (19420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19420)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (19420)Memory used [KB]: 5373
% 0.21/0.49  % (19420)Time elapsed: 0.073 s
% 0.21/0.49  % (19420)------------------------------
% 0.21/0.49  % (19420)------------------------------
% 0.21/0.49  % (19427)Refutation not found, incomplete strategy% (19427)------------------------------
% 0.21/0.49  % (19427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19427)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (19427)Memory used [KB]: 5373
% 0.21/0.49  % (19427)Time elapsed: 0.032 s
% 0.21/0.49  % (19427)------------------------------
% 0.21/0.49  % (19427)------------------------------
% 0.21/0.49  % (19418)Refutation not found, incomplete strategy% (19418)------------------------------
% 0.21/0.49  % (19418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19418)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (19418)Memory used [KB]: 895
% 0.21/0.49  % (19418)Time elapsed: 0.077 s
% 0.21/0.49  % (19418)------------------------------
% 0.21/0.49  % (19418)------------------------------
% 0.21/0.49  % (19412)Success in time 0.13 s
%------------------------------------------------------------------------------
