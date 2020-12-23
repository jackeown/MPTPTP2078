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
% DateTime   : Thu Dec  3 13:16:16 EST 2020

% Result     : CounterSatisfiable 0.11s
% Output     : Saturation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   33 (  33 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u50,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) )).

tff(u49,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) )).

tff(u48,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) )).

tff(u47,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) )).

tff(u46,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u45,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u44,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u43,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u42,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u41,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) )).

tff(u40,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u39,negated_conjecture,(
    v2_yellow_0(sK0) )).

tff(u38,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK0,u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,u1_struct_0(sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n008.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 10:52:30 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.40  % (7370)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.11/0.40  % (7375)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.11/0.40  % (7376)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.11/0.40  % (7375)Refutation not found, incomplete strategy% (7375)------------------------------
% 0.11/0.40  % (7375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.40  % (7375)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.40  
% 0.11/0.40  % (7375)Memory used [KB]: 895
% 0.11/0.40  % (7375)Time elapsed: 0.038 s
% 0.11/0.40  % (7375)------------------------------
% 0.11/0.40  % (7375)------------------------------
% 0.11/0.40  % SZS status CounterSatisfiable for theBenchmark
% 0.11/0.40  % (7376)# SZS output start Saturation.
% 0.11/0.41  tff(u50,axiom,
% 0.11/0.41      (![X1, X0] : ((~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))))).
% 0.11/0.41  
% 0.11/0.41  tff(u49,axiom,
% 0.11/0.41      (![X1, X3, X0, X2] : ((~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X3,X2) | ~r2_lattice3(X0,X1,X2))))).
% 0.11/0.41  
% 0.11/0.41  tff(u48,axiom,
% 0.11/0.41      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2))))).
% 0.11/0.41  
% 0.11/0.41  tff(u47,axiom,
% 0.11/0.41      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(sK1(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2))))).
% 0.11/0.41  
% 0.11/0.41  tff(u46,axiom,
% 0.11/0.41      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.11/0.41  
% 0.11/0.41  tff(u45,negated_conjecture,
% 0.11/0.41      ~v2_struct_0(sK0)).
% 0.11/0.41  
% 0.11/0.41  tff(u44,negated_conjecture,
% 0.11/0.41      l1_struct_0(sK0)).
% 0.11/0.41  
% 0.11/0.41  tff(u43,axiom,
% 0.11/0.41      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.11/0.41  
% 0.11/0.41  tff(u42,negated_conjecture,
% 0.11/0.41      l1_orders_2(sK0)).
% 0.11/0.41  
% 0.11/0.41  tff(u41,axiom,
% 0.11/0.41      (![X1, X0, X2] : ((~r1_orders_2(X0,sK1(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2))))).
% 0.11/0.41  
% 0.11/0.41  tff(u40,negated_conjecture,
% 0.11/0.41      v5_orders_2(sK0)).
% 0.11/0.41  
% 0.11/0.41  tff(u39,negated_conjecture,
% 0.11/0.41      v2_yellow_0(sK0)).
% 0.11/0.41  
% 0.11/0.41  tff(u38,negated_conjecture,
% 0.11/0.41      ((~~r1_yellow_0(sK0,u1_struct_0(sK0))) | ~r1_yellow_0(sK0,u1_struct_0(sK0)))).
% 0.11/0.41  
% 0.11/0.41  % (7376)# SZS output end Saturation.
% 0.11/0.41  % (7376)------------------------------
% 0.11/0.41  % (7376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.41  % (7376)Termination reason: Satisfiable
% 0.11/0.41  
% 0.11/0.41  % (7376)Memory used [KB]: 5245
% 0.11/0.41  % (7376)Time elapsed: 0.038 s
% 0.11/0.41  % (7376)------------------------------
% 0.11/0.41  % (7376)------------------------------
% 0.18/0.41  % (7369)Success in time 0.071 s
%------------------------------------------------------------------------------
