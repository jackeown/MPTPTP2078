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
% DateTime   : Thu Dec  3 13:16:05 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (30884)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.21/0.46  % (30876)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.46  % (30876)Refutation not found, incomplete strategy% (30876)------------------------------
% 0.21/0.46  % (30876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (30876)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (30876)Memory used [KB]: 9850
% 0.21/0.46  % (30876)Time elapsed: 0.056 s
% 0.21/0.46  % (30876)------------------------------
% 0.21/0.46  % (30876)------------------------------
% 0.21/0.46  % (30871)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.47  % (30884)Refutation not found, incomplete strategy% (30884)------------------------------
% 0.21/0.47  % (30884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (30884)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (30884)Memory used [KB]: 9850
% 0.21/0.47  % (30884)Time elapsed: 0.056 s
% 0.21/0.47  % (30884)------------------------------
% 0.21/0.47  % (30884)------------------------------
% 0.21/0.47  % (30881)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.47  % (30881)Refutation not found, incomplete strategy% (30881)------------------------------
% 0.21/0.47  % (30881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (30881)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (30881)Memory used [KB]: 5373
% 0.21/0.47  % (30881)Time elapsed: 0.030 s
% 0.21/0.47  % (30881)------------------------------
% 0.21/0.47  % (30881)------------------------------
% 0.21/0.48  % (30869)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.48  % (30879)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.48  % (30867)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.48  % (30867)Refutation not found, incomplete strategy% (30867)------------------------------
% 0.21/0.48  % (30867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30867)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (30867)Memory used [KB]: 5245
% 0.21/0.48  % (30867)Time elapsed: 0.064 s
% 0.21/0.48  % (30867)------------------------------
% 0.21/0.48  % (30867)------------------------------
% 0.21/0.48  % (30873)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.48  % (30873)# SZS output start Saturation.
% 0.21/0.48  tff(u46,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~r1_tarski(X0,X2) | r2_hidden(sK4(X0,X1),X2) | r1_tarski(X0,X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u45,negated_conjecture,
% 0.21/0.48      (![X1, X0] : ((~r1_tarski(sK2,X1) | r2_hidden(sK4(sK1,X0),X1) | r1_tarski(sK1,X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u44,negated_conjecture,
% 0.21/0.48      r1_tarski(sK1,sK2)).
% 0.21/0.48  
% 0.21/0.48  tff(u43,axiom,
% 0.21/0.48      (![X0] : (r1_tarski(X0,X0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u42,axiom,
% 0.21/0.48      (![X1, X0] : ((~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u41,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u40,axiom,
% 0.21/0.48      (![X1, X0] : ((r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u39,negated_conjecture,
% 0.21/0.48      (![X0] : ((r2_hidden(sK4(sK1,X0),sK2) | r1_tarski(sK1,X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u38,negated_conjecture,
% 0.21/0.48      l1_orders_2(sK0)).
% 0.21/0.48  
% 0.21/0.48  tff(u37,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X2,X3) | ~r1_lattice3(X0,X1,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u36,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u35,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(sK3(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u34,negated_conjecture,
% 0.21/0.48      ~r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))).
% 0.21/0.48  
% 0.21/0.48  tff(u33,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u32,negated_conjecture,
% 0.21/0.48      r2_yellow_0(sK0,sK1)).
% 0.21/0.48  
% 0.21/0.48  tff(u31,negated_conjecture,
% 0.21/0.48      r2_yellow_0(sK0,sK2)).
% 0.21/0.48  
% 0.21/0.48  % (30873)# SZS output end Saturation.
% 0.21/0.48  % (30873)------------------------------
% 0.21/0.48  % (30873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30873)Termination reason: Satisfiable
% 0.21/0.48  
% 0.21/0.48  % (30873)Memory used [KB]: 5373
% 0.21/0.48  % (30873)Time elapsed: 0.034 s
% 0.21/0.48  % (30873)------------------------------
% 0.21/0.48  % (30873)------------------------------
% 0.21/0.48  % (30866)Success in time 0.127 s
%------------------------------------------------------------------------------
