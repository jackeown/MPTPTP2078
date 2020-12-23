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
% DateTime   : Thu Dec  3 13:16:17 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    6 (   6 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    0
%              Number of atoms          :    6 (   6 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    2 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u16,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u15,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u14,negated_conjecture,(
    v1_yellow_0(sK0) )).

tff(u13,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u12,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u11,negated_conjecture,(
    ~ r1_orders_2(sK0,k3_yellow_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:47:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (10049)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.44  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.44  % (10049)# SZS output start Saturation.
% 0.21/0.44  tff(u16,negated_conjecture,
% 0.21/0.44      ~v2_struct_0(sK0)).
% 0.21/0.44  
% 0.21/0.44  tff(u15,negated_conjecture,
% 0.21/0.44      v5_orders_2(sK0)).
% 0.21/0.44  
% 0.21/0.44  tff(u14,negated_conjecture,
% 0.21/0.44      v1_yellow_0(sK0)).
% 0.21/0.44  
% 0.21/0.44  tff(u13,negated_conjecture,
% 0.21/0.44      l1_orders_2(sK0)).
% 0.21/0.44  
% 0.21/0.44  tff(u12,negated_conjecture,
% 0.21/0.44      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.44  
% 0.21/0.44  tff(u11,negated_conjecture,
% 0.21/0.44      ~r1_orders_2(sK0,k3_yellow_0(sK0),sK1)).
% 0.21/0.44  
% 0.21/0.44  % (10049)# SZS output end Saturation.
% 0.21/0.44  % (10049)------------------------------
% 0.21/0.44  % (10049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (10049)Termination reason: Satisfiable
% 0.21/0.44  
% 0.21/0.44  % (10049)Memory used [KB]: 5245
% 0.21/0.44  % (10049)Time elapsed: 0.004 s
% 0.21/0.44  % (10049)------------------------------
% 0.21/0.44  % (10049)------------------------------
% 0.21/0.44  % (10040)Success in time 0.086 s
%------------------------------------------------------------------------------
