%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:56 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u32,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u31,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u30,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u29,negated_conjecture,(
    l1_waybel_0(sK1,sK0) )).

tff(u28,negated_conjecture,
    ( ~ ~ v11_waybel_0(sK1,sK0)
    | ~ v11_waybel_0(sK1,sK0) )).

tff(u27,negated_conjecture,
    ( ~ ~ v11_waybel_0(sK1,sK0)
    | ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK1))
        | m1_subset_1(sK3(X2),u1_struct_0(sK1)) ) )).

tff(u26,negated_conjecture,
    ( ~ ~ v11_waybel_0(sK1,sK0)
    | ! [X2,X4] :
        ( ~ r1_orders_2(sK1,sK3(X2),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X4),k2_waybel_0(sK0,sK1,X2)) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (30721)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.46  % (30721)# SZS output start Saturation.
% 0.20/0.46  tff(u32,negated_conjecture,
% 0.20/0.46      ~v2_struct_0(sK1)).
% 0.20/0.46  
% 0.20/0.46  tff(u31,negated_conjecture,
% 0.20/0.46      ~v2_struct_0(sK0)).
% 0.20/0.46  
% 0.20/0.46  tff(u30,negated_conjecture,
% 0.20/0.46      l1_orders_2(sK0)).
% 0.20/0.46  
% 0.20/0.46  tff(u29,negated_conjecture,
% 0.20/0.46      l1_waybel_0(sK1,sK0)).
% 0.20/0.46  
% 0.20/0.46  tff(u28,negated_conjecture,
% 0.20/0.46      ((~~v11_waybel_0(sK1,sK0)) | ~v11_waybel_0(sK1,sK0))).
% 0.20/0.46  
% 0.20/0.46  tff(u27,negated_conjecture,
% 0.20/0.46      ((~~v11_waybel_0(sK1,sK0)) | (![X2] : ((~m1_subset_1(X2,u1_struct_0(sK1)) | m1_subset_1(sK3(X2),u1_struct_0(sK1))))))).
% 0.20/0.46  
% 0.20/0.46  tff(u26,negated_conjecture,
% 0.20/0.46      ((~~v11_waybel_0(sK1,sK0)) | (![X2, X4] : ((~r1_orders_2(sK1,sK3(X2),X4) | ~m1_subset_1(X4,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X4),k2_waybel_0(sK0,sK1,X2))))))).
% 0.20/0.46  
% 0.20/0.46  % (30721)# SZS output end Saturation.
% 0.20/0.46  % (30721)------------------------------
% 0.20/0.46  % (30721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (30721)Termination reason: Satisfiable
% 0.20/0.46  
% 0.20/0.46  % (30721)Memory used [KB]: 5245
% 0.20/0.46  % (30721)Time elapsed: 0.052 s
% 0.20/0.46  % (30721)------------------------------
% 0.20/0.46  % (30721)------------------------------
% 0.20/0.47  % (30713)Success in time 0.11 s
%------------------------------------------------------------------------------
