%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:18 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :    6 (   6 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    0
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u20,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u19,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u18,negated_conjecture,(
    ! [X3] :
      ( ~ r1_lattice3(sK0,sK1,X3)
      | r1_lattice3(sK0,sK2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) )).

tff(u17,negated_conjecture,(
    ! [X3] :
      ( ~ r1_lattice3(sK0,sK2,X3)
      | r1_lattice3(sK0,sK1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) )).

tff(u16,negated_conjecture,(
    ~ r2_yellow_0(sK0,sK2) )).

tff(u15,negated_conjecture,(
    r2_yellow_0(sK0,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:56:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (26438)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.22/0.48  % (26430)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.48  % (26438)Refutation not found, incomplete strategy% (26438)------------------------------
% 0.22/0.48  % (26438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (26438)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (26438)Memory used [KB]: 5245
% 0.22/0.48  % (26438)Time elapsed: 0.062 s
% 0.22/0.48  % (26438)------------------------------
% 0.22/0.48  % (26438)------------------------------
% 0.22/0.48  % (26427)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.48  % (26430)Refutation not found, incomplete strategy% (26430)------------------------------
% 0.22/0.48  % (26430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (26430)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (26430)Memory used [KB]: 9722
% 0.22/0.48  % (26430)Time elapsed: 0.062 s
% 0.22/0.48  % (26430)------------------------------
% 0.22/0.48  % (26430)------------------------------
% 0.22/0.49  % (26427)Refutation not found, incomplete strategy% (26427)------------------------------
% 0.22/0.49  % (26427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (26427)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (26427)Memory used [KB]: 5245
% 0.22/0.49  % (26427)Time elapsed: 0.072 s
% 0.22/0.49  % (26427)------------------------------
% 0.22/0.49  % (26427)------------------------------
% 0.22/0.50  % (26446)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.22/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.50  % (26446)# SZS output start Saturation.
% 0.22/0.50  tff(u20,negated_conjecture,
% 0.22/0.50      ~v2_struct_0(sK0)).
% 0.22/0.50  
% 0.22/0.50  tff(u19,negated_conjecture,
% 0.22/0.50      l1_orders_2(sK0)).
% 0.22/0.50  
% 0.22/0.50  tff(u18,negated_conjecture,
% 0.22/0.50      (![X3] : ((~r1_lattice3(sK0,sK1,X3) | r1_lattice3(sK0,sK2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)))))).
% 0.22/0.50  
% 0.22/0.50  tff(u17,negated_conjecture,
% 0.22/0.50      (![X3] : ((~r1_lattice3(sK0,sK2,X3) | r1_lattice3(sK0,sK1,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)))))).
% 0.22/0.50  
% 0.22/0.50  tff(u16,negated_conjecture,
% 0.22/0.50      ~r2_yellow_0(sK0,sK2)).
% 0.22/0.50  
% 0.22/0.50  tff(u15,negated_conjecture,
% 0.22/0.50      r2_yellow_0(sK0,sK1)).
% 0.22/0.50  
% 0.22/0.50  % (26446)# SZS output end Saturation.
% 0.22/0.50  % (26446)------------------------------
% 0.22/0.50  % (26446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26446)Termination reason: Satisfiable
% 0.22/0.50  
% 0.22/0.50  % (26446)Memory used [KB]: 5245
% 0.22/0.50  % (26446)Time elapsed: 0.082 s
% 0.22/0.50  % (26446)------------------------------
% 0.22/0.50  % (26446)------------------------------
% 0.22/0.50  % (26426)Success in time 0.133 s
%------------------------------------------------------------------------------
