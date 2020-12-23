%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:16 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:07:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (4637)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.46  % (4637)Refutation not found, incomplete strategy% (4637)------------------------------
% 0.20/0.46  % (4637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (4637)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (4637)Memory used [KB]: 5373
% 0.20/0.46  % (4637)Time elapsed: 0.006 s
% 0.20/0.46  % (4637)------------------------------
% 0.20/0.46  % (4637)------------------------------
% 0.20/0.46  % (4629)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.46  % (4629)# SZS output start Saturation.
% 0.20/0.46  tff(u50,axiom,
% 0.20/0.46      (![X1, X0] : ((~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))))).
% 0.20/0.46  
% 0.20/0.46  tff(u49,axiom,
% 0.20/0.46      (![X1, X3, X0, X2] : ((~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X3,X2) | ~r2_lattice3(X0,X1,X2))))).
% 0.20/0.46  
% 0.20/0.46  tff(u48,axiom,
% 0.20/0.46      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2))))).
% 0.20/0.46  
% 0.20/0.46  tff(u47,axiom,
% 0.20/0.46      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(sK1(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2))))).
% 0.20/0.46  
% 0.20/0.46  tff(u46,axiom,
% 0.20/0.46      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u45,negated_conjecture,
% 0.20/0.46      ~v2_struct_0(sK0)).
% 0.20/0.46  
% 0.20/0.46  tff(u44,negated_conjecture,
% 0.20/0.46      l1_struct_0(sK0)).
% 0.20/0.46  
% 0.20/0.46  tff(u43,axiom,
% 0.20/0.46      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u42,negated_conjecture,
% 0.20/0.46      l1_orders_2(sK0)).
% 0.20/0.46  
% 0.20/0.46  tff(u41,axiom,
% 0.20/0.46      (![X1, X0, X2] : ((~r1_orders_2(X0,sK1(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2))))).
% 0.20/0.46  
% 0.20/0.46  tff(u40,negated_conjecture,
% 0.20/0.46      v5_orders_2(sK0)).
% 0.20/0.46  
% 0.20/0.46  tff(u39,negated_conjecture,
% 0.20/0.46      v2_yellow_0(sK0)).
% 0.20/0.46  
% 0.20/0.46  tff(u38,negated_conjecture,
% 0.20/0.46      ((~~r1_yellow_0(sK0,u1_struct_0(sK0))) | ~r1_yellow_0(sK0,u1_struct_0(sK0)))).
% 0.20/0.46  
% 0.20/0.46  % (4629)# SZS output end Saturation.
% 0.20/0.46  % (4629)------------------------------
% 0.20/0.46  % (4629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (4629)Termination reason: Satisfiable
% 0.20/0.46  
% 0.20/0.46  % (4629)Memory used [KB]: 5245
% 0.20/0.46  % (4629)Time elapsed: 0.026 s
% 0.20/0.46  % (4629)------------------------------
% 0.20/0.46  % (4629)------------------------------
% 0.20/0.47  % (4622)Success in time 0.113 s
%------------------------------------------------------------------------------
