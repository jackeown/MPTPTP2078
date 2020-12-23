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
% DateTime   : Thu Dec  3 13:16:17 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:19:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (26376)WARNING: option uwaf not known.
% 0.22/0.48  % (26372)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.48  % (26372)# SZS output start Saturation.
% 0.22/0.48  tff(u16,negated_conjecture,
% 0.22/0.48      ~v2_struct_0(sK0)).
% 0.22/0.48  
% 0.22/0.48  tff(u15,negated_conjecture,
% 0.22/0.48      v5_orders_2(sK0)).
% 0.22/0.48  
% 0.22/0.48  tff(u14,negated_conjecture,
% 0.22/0.48      v1_yellow_0(sK0)).
% 0.22/0.48  
% 0.22/0.48  tff(u13,negated_conjecture,
% 0.22/0.48      l1_orders_2(sK0)).
% 0.22/0.48  
% 0.22/0.48  tff(u12,negated_conjecture,
% 0.22/0.48      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.48  
% 0.22/0.48  tff(u11,negated_conjecture,
% 0.22/0.48      ~r1_orders_2(sK0,k3_yellow_0(sK0),sK1)).
% 0.22/0.48  
% 0.22/0.48  % (26372)# SZS output end Saturation.
% 0.22/0.48  % (26372)------------------------------
% 0.22/0.48  % (26372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (26372)Termination reason: Satisfiable
% 0.22/0.48  
% 0.22/0.48  % (26372)Memory used [KB]: 5245
% 0.22/0.48  % (26372)Time elapsed: 0.064 s
% 0.22/0.48  % (26372)------------------------------
% 0.22/0.48  % (26372)------------------------------
% 0.22/0.48  % (26363)Success in time 0.118 s
%------------------------------------------------------------------------------
