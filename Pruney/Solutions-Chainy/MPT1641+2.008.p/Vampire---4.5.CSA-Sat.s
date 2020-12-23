%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:01 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    0
%              Number of atoms          :   30 (  30 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u38,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r1_tarski(X1,X2) ) )).

tff(u37,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK3(X0,X1,X2),X0)
      | r1_tarski(X1,X2) ) )).

tff(u36,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u35,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u34,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) )).

tff(u33,negated_conjecture,(
    ~ r1_tarski(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)) )).

tff(u32,negated_conjecture,(
    v4_orders_2(sK0) )).

tff(u31,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u30,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3) ) )).

tff(u29,negated_conjecture,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,sK1,X0) ) )).

tff(u28,negated_conjecture,(
    r1_orders_2(sK0,sK1,sK2) )).

tff(u27,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (21303)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.47  % (21306)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.47  % (21295)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.48  % (21306)Refutation not found, incomplete strategy% (21306)------------------------------
% 0.22/0.48  % (21306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (21306)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (21306)Memory used [KB]: 895
% 0.22/0.48  % (21306)Time elapsed: 0.007 s
% 0.22/0.48  % (21306)------------------------------
% 0.22/0.48  % (21306)------------------------------
% 0.22/0.48  % (21296)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.48  % (21296)# SZS output start Saturation.
% 0.22/0.48  tff(u38,axiom,
% 0.22/0.48      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK3(X0,X1,X2),X1) | r1_tarski(X1,X2))))).
% 0.22/0.48  
% 0.22/0.48  tff(u37,axiom,
% 0.22/0.48      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK3(X0,X1,X2),X0) | r1_tarski(X1,X2))))).
% 0.22/0.48  
% 0.22/0.48  tff(u36,negated_conjecture,
% 0.22/0.48      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.22/0.48  
% 0.22/0.48  tff(u35,negated_conjecture,
% 0.22/0.48      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.48  
% 0.22/0.48  tff(u34,axiom,
% 0.22/0.48      (![X1, X0, X2] : ((~r2_hidden(sK3(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2))))).
% 0.22/0.48  
% 0.22/0.48  tff(u33,negated_conjecture,
% 0.22/0.48      ~r1_tarski(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2))).
% 0.22/0.48  
% 0.22/0.48  tff(u32,negated_conjecture,
% 0.22/0.48      v4_orders_2(sK0)).
% 0.22/0.48  
% 0.22/0.48  tff(u31,negated_conjecture,
% 0.22/0.48      l1_orders_2(sK0)).
% 0.22/0.48  
% 0.22/0.48  tff(u30,axiom,
% 0.22/0.48      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v4_orders_2(X0) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X1,X3))))).
% 0.22/0.48  
% 0.22/0.48  tff(u29,negated_conjecture,
% 0.22/0.48      (![X0] : ((~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u28,negated_conjecture,
% 0.22/0.48      r1_orders_2(sK0,sK1,sK2)).
% 0.22/0.48  
% 0.22/0.48  tff(u27,negated_conjecture,
% 0.22/0.48      ~v2_struct_0(sK0)).
% 0.22/0.48  
% 0.22/0.48  % (21296)# SZS output end Saturation.
% 0.22/0.48  % (21296)------------------------------
% 0.22/0.48  % (21296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (21296)Termination reason: Satisfiable
% 0.22/0.48  
% 0.22/0.48  % (21296)Memory used [KB]: 5373
% 0.22/0.48  % (21296)Time elapsed: 0.005 s
% 0.22/0.48  % (21296)------------------------------
% 0.22/0.48  % (21296)------------------------------
% 0.22/0.48  % (21287)Success in time 0.123 s
%------------------------------------------------------------------------------
