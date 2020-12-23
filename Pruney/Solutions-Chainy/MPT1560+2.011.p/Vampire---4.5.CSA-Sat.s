%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:07 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :    8 (   8 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    0
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u48,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k2_tarski(sK1,sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

tff(u47,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u46,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u45,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u44,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u43,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u42,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) )).

tff(u41,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:34:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (26050)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.46  % (26050)# SZS output start Saturation.
% 0.22/0.46  tff(u48,negated_conjecture,
% 0.22/0.46      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)))).
% 0.22/0.46  
% 0.22/0.46  tff(u47,negated_conjecture,
% 0.22/0.46      ~v2_struct_0(sK0)).
% 0.22/0.46  
% 0.22/0.46  tff(u46,negated_conjecture,
% 0.22/0.46      l1_struct_0(sK0)).
% 0.22/0.46  
% 0.22/0.46  tff(u45,axiom,
% 0.22/0.46      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.22/0.46  
% 0.22/0.46  tff(u44,axiom,
% 0.22/0.46      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.22/0.46  
% 0.22/0.46  tff(u43,negated_conjecture,
% 0.22/0.46      l1_orders_2(sK0)).
% 0.22/0.46  
% 0.22/0.46  tff(u42,axiom,
% 0.22/0.46      (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k2_tarski(X1,X1)) | v1_xboole_0(X0))))).
% 0.22/0.46  
% 0.22/0.46  tff(u41,negated_conjecture,
% 0.22/0.46      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.46  
% 0.22/0.46  % (26050)# SZS output end Saturation.
% 0.22/0.46  % (26050)------------------------------
% 0.22/0.46  % (26050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (26050)Termination reason: Satisfiable
% 0.22/0.46  
% 0.22/0.46  % (26050)Memory used [KB]: 10618
% 0.22/0.46  % (26050)Time elapsed: 0.029 s
% 0.22/0.46  % (26050)------------------------------
% 0.22/0.46  % (26050)------------------------------
% 0.22/0.46  % (26040)Success in time 0.102 s
%------------------------------------------------------------------------------
