%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:21 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    0
%              Number of atoms          :   36 (  36 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u70,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u69,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_xboole_0(u1_struct_0(sK1)) )).

tff(u68,negated_conjecture,
    ( ~ ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK2) )).

tff(u67,negated_conjecture,(
    ~ m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u66,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u65,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) )).

tff(u64,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) )).

tff(u63,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u62,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) )).

tff(u61,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X0,X2)
      | m1_subset_1(X0,X1)
      | ~ v1_xboole_0(X2)
      | ~ v1_xboole_0(k1_zfmisc_1(X1)) ) )).

tff(u60,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u59,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK1))
    | r2_hidden(sK2,u1_struct_0(sK1)) )).

tff(u58,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u57,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u56,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u55,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u54,negated_conjecture,(
    l1_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:51:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (6907)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.46  % (6899)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.46  % (6899)# SZS output start Saturation.
% 0.21/0.46  tff(u70,axiom,
% 0.21/0.46      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u69,negated_conjecture,
% 0.21/0.46      ((~~v1_xboole_0(u1_struct_0(sK1))) | ~v1_xboole_0(u1_struct_0(sK1)))).
% 0.21/0.46  
% 0.21/0.46  tff(u68,negated_conjecture,
% 0.21/0.46      ((~~v1_xboole_0(sK2)) | ~v1_xboole_0(sK2))).
% 0.21/0.46  
% 0.21/0.46  tff(u67,negated_conjecture,
% 0.21/0.46      ~m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.21/0.46  
% 0.21/0.46  tff(u66,axiom,
% 0.21/0.46      (![X1, X0] : ((~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u65,axiom,
% 0.21/0.46      (![X1, X0] : ((~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u64,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1))))).
% 0.21/0.46  
% 0.21/0.46  tff(u63,negated_conjecture,
% 0.21/0.46      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.21/0.46  
% 0.21/0.46  tff(u62,axiom,
% 0.21/0.46      (![X1, X0] : ((m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u61,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((~r2_hidden(X0,X2) | m1_subset_1(X0,X1) | ~v1_xboole_0(X2) | ~v1_xboole_0(k1_zfmisc_1(X1)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u60,axiom,
% 0.21/0.46      (![X1, X0] : ((~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u59,negated_conjecture,
% 0.21/0.46      ((~~v1_xboole_0(u1_struct_0(sK1))) | r2_hidden(sK2,u1_struct_0(sK1)))).
% 0.21/0.46  
% 0.21/0.46  tff(u58,negated_conjecture,
% 0.21/0.46      ~v2_struct_0(sK0)).
% 0.21/0.46  
% 0.21/0.46  tff(u57,negated_conjecture,
% 0.21/0.46      ~v2_struct_0(sK1)).
% 0.21/0.46  
% 0.21/0.46  tff(u56,negated_conjecture,
% 0.21/0.46      l1_struct_0(sK0)).
% 0.21/0.46  
% 0.21/0.46  tff(u55,axiom,
% 0.21/0.46      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u54,negated_conjecture,
% 0.21/0.46      l1_orders_2(sK0)).
% 0.21/0.46  
% 0.21/0.46  % (6899)# SZS output end Saturation.
% 0.21/0.46  % (6899)------------------------------
% 0.21/0.46  % (6899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (6899)Termination reason: Satisfiable
% 0.21/0.46  
% 0.21/0.46  % (6899)Memory used [KB]: 5373
% 0.21/0.46  % (6899)Time elapsed: 0.048 s
% 0.21/0.46  % (6899)------------------------------
% 0.21/0.46  % (6899)------------------------------
% 0.21/0.46  % (6891)Success in time 0.104 s
%------------------------------------------------------------------------------
