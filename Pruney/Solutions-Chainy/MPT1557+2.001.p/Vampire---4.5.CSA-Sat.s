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
% DateTime   : Thu Dec  3 13:16:04 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    0
%              Number of atoms          :   39 (  39 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u46,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK4(X0,X1),X2)
      | r1_tarski(X0,X1) ) )).

tff(u45,negated_conjecture,(
    ! [X1,X0] :
      ( ~ r1_tarski(sK2,X1)
      | r2_hidden(sK4(sK1,X0),X1)
      | r1_tarski(sK1,X0) ) )).

tff(u44,negated_conjecture,(
    r1_tarski(sK1,sK2) )).

tff(u43,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u42,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) )).

tff(u41,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) )).

tff(u40,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) )).

tff(u39,negated_conjecture,(
    ! [X0] :
      ( r2_hidden(sK4(sK1,X0),sK2)
      | r1_tarski(sK1,X0) ) )).

tff(u38,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u37,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X2) ) )).

tff(u36,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) )).

tff(u35,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2) ) )).

tff(u34,negated_conjecture,(
    ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) )).

tff(u33,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) )).

tff(u32,negated_conjecture,(
    r2_yellow_0(sK0,sK1) )).

tff(u31,negated_conjecture,(
    r2_yellow_0(sK0,sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (12123)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.46  % (12123)Refutation not found, incomplete strategy% (12123)------------------------------
% 0.20/0.46  % (12123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (12122)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.46  % (12123)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (12123)Memory used [KB]: 5373
% 0.20/0.46  % (12123)Time elapsed: 0.062 s
% 0.20/0.46  % (12123)------------------------------
% 0.20/0.46  % (12123)------------------------------
% 0.20/0.46  % (12118)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.20/0.46  % (12118)Refutation not found, incomplete strategy% (12118)------------------------------
% 0.20/0.46  % (12118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (12118)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (12118)Memory used [KB]: 9850
% 0.20/0.46  % (12118)Time elapsed: 0.056 s
% 0.20/0.46  % (12118)------------------------------
% 0.20/0.46  % (12118)------------------------------
% 0.20/0.47  % (12121)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.20/0.47  % (12115)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.47  % (12115)# SZS output start Saturation.
% 0.20/0.47  tff(u46,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((~r1_tarski(X0,X2) | r2_hidden(sK4(X0,X1),X2) | r1_tarski(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u45,negated_conjecture,
% 0.20/0.47      (![X1, X0] : ((~r1_tarski(sK2,X1) | r2_hidden(sK4(sK1,X0),X1) | r1_tarski(sK1,X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u44,negated_conjecture,
% 0.20/0.47      r1_tarski(sK1,sK2)).
% 0.20/0.47  
% 0.20/0.47  tff(u43,axiom,
% 0.20/0.47      (![X0] : (r1_tarski(X0,X0)))).
% 0.20/0.47  
% 0.20/0.47  tff(u42,axiom,
% 0.20/0.47      (![X1, X0] : ((~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u41,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u40,axiom,
% 0.20/0.47      (![X1, X0] : ((r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u39,negated_conjecture,
% 0.20/0.47      (![X0] : ((r2_hidden(sK4(sK1,X0),sK2) | r1_tarski(sK1,X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u38,negated_conjecture,
% 0.20/0.47      l1_orders_2(sK0)).
% 0.20/0.47  
% 0.20/0.47  tff(u37,axiom,
% 0.20/0.47      (![X1, X3, X0, X2] : ((~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X2,X3) | ~r1_lattice3(X0,X1,X2))))).
% 0.20/0.47  
% 0.20/0.47  tff(u36,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2))))).
% 0.20/0.47  
% 0.20/0.47  tff(u35,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(sK3(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2))))).
% 0.20/0.47  
% 0.20/0.47  tff(u34,negated_conjecture,
% 0.20/0.47      ~r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))).
% 0.20/0.47  
% 0.20/0.47  tff(u33,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2))))).
% 0.20/0.47  
% 0.20/0.47  tff(u32,negated_conjecture,
% 0.20/0.47      r2_yellow_0(sK0,sK1)).
% 0.20/0.47  
% 0.20/0.47  tff(u31,negated_conjecture,
% 0.20/0.47      r2_yellow_0(sK0,sK2)).
% 0.20/0.47  
% 0.20/0.47  % (12115)# SZS output end Saturation.
% 0.20/0.47  % (12115)------------------------------
% 0.20/0.47  % (12115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (12115)Termination reason: Satisfiable
% 0.20/0.47  
% 0.20/0.47  % (12115)Memory used [KB]: 5373
% 0.20/0.47  % (12115)Time elapsed: 0.031 s
% 0.20/0.47  % (12115)------------------------------
% 0.20/0.47  % (12115)------------------------------
% 0.20/0.47  % (12120)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.20/0.47  % (12107)Success in time 0.118 s
%------------------------------------------------------------------------------
