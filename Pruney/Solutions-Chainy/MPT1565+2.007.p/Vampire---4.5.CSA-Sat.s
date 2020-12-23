%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:16 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    0
%              Number of atoms          :   42 (  42 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u55,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u54,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(X1)
      | m1_subset_1(X1,X0) ) )).

tff(u53,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u52,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) )).

tff(u51,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) )).

tff(u50,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) )).

tff(u49,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) )).

tff(u48,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) )).

tff(u47,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u46,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u45,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u44,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u43,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) )).

tff(u42,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u41,negated_conjecture,(
    v2_yellow_0(sK0) )).

tff(u40,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK0,u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,u1_struct_0(sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:00:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (18887)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.47  % (18881)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.47  % (18887)# SZS output start Saturation.
% 0.21/0.47  tff(u55,axiom,
% 0.21/0.47      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u54,axiom,
% 0.21/0.47      (![X1, X0] : ((~v1_xboole_0(X0) | ~v1_xboole_0(X1) | m1_subset_1(X1,X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u53,axiom,
% 0.21/0.47      (![X1, X0] : ((~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u52,axiom,
% 0.21/0.47      (![X1, X0] : ((~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u51,axiom,
% 0.21/0.47      (![X1, X3, X0, X2] : ((~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X3,X2) | ~r2_lattice3(X0,X1,X2))))).
% 0.21/0.47  
% 0.21/0.47  tff(u50,axiom,
% 0.21/0.47      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2))))).
% 0.21/0.47  
% 0.21/0.47  tff(u49,axiom,
% 0.21/0.47      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(sK1(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2))))).
% 0.21/0.47  
% 0.21/0.47  tff(u48,axiom,
% 0.21/0.47      (![X1, X0] : ((~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u47,negated_conjecture,
% 0.21/0.47      ~v2_struct_0(sK0)).
% 0.21/0.47  
% 0.21/0.47  tff(u46,negated_conjecture,
% 0.21/0.47      l1_struct_0(sK0)).
% 0.21/0.47  
% 0.21/0.47  tff(u45,axiom,
% 0.21/0.47      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u44,negated_conjecture,
% 0.21/0.47      l1_orders_2(sK0)).
% 0.21/0.47  
% 0.21/0.47  tff(u43,axiom,
% 0.21/0.47      (![X1, X0, X2] : ((~r1_orders_2(X0,sK1(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2))))).
% 0.21/0.47  
% 0.21/0.47  tff(u42,negated_conjecture,
% 0.21/0.47      v5_orders_2(sK0)).
% 0.21/0.47  
% 0.21/0.47  tff(u41,negated_conjecture,
% 0.21/0.47      v2_yellow_0(sK0)).
% 0.21/0.47  
% 0.21/0.47  tff(u40,negated_conjecture,
% 0.21/0.47      ((~~r1_yellow_0(sK0,u1_struct_0(sK0))) | ~r1_yellow_0(sK0,u1_struct_0(sK0)))).
% 0.21/0.47  
% 0.21/0.47  % (18887)# SZS output end Saturation.
% 0.21/0.47  % (18887)------------------------------
% 0.21/0.47  % (18887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (18887)Termination reason: Satisfiable
% 0.21/0.47  
% 0.21/0.47  % (18887)Memory used [KB]: 5373
% 0.21/0.47  % (18887)Time elapsed: 0.054 s
% 0.21/0.47  % (18887)------------------------------
% 0.21/0.47  % (18887)------------------------------
% 0.21/0.47  % (18881)Refutation not found, incomplete strategy% (18881)------------------------------
% 0.21/0.47  % (18881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (18881)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (18881)Memory used [KB]: 5373
% 0.21/0.47  % (18881)Time elapsed: 0.050 s
% 0.21/0.47  % (18881)------------------------------
% 0.21/0.47  % (18881)------------------------------
% 0.21/0.47  % (18880)Success in time 0.11 s
%------------------------------------------------------------------------------
