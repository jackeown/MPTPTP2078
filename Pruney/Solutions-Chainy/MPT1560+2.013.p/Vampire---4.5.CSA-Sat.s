%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:07 EST 2020

% Result     : CounterSatisfiable 0.23s
% Output     : Saturation 0.23s
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
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 13:41:26 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.46  % (831)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.23/0.46  % (831)# SZS output start Saturation.
% 0.23/0.46  tff(u48,negated_conjecture,
% 0.23/0.46      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)))).
% 0.23/0.46  
% 0.23/0.46  tff(u47,negated_conjecture,
% 0.23/0.46      ~v2_struct_0(sK0)).
% 0.23/0.46  
% 0.23/0.46  tff(u46,negated_conjecture,
% 0.23/0.46      l1_struct_0(sK0)).
% 0.23/0.46  
% 0.23/0.46  tff(u45,axiom,
% 0.23/0.46      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.23/0.46  
% 0.23/0.46  tff(u44,axiom,
% 0.23/0.46      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.23/0.46  
% 0.23/0.46  tff(u43,negated_conjecture,
% 0.23/0.46      l1_orders_2(sK0)).
% 0.23/0.46  
% 0.23/0.46  tff(u42,axiom,
% 0.23/0.46      (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k2_tarski(X1,X1)) | v1_xboole_0(X0))))).
% 0.23/0.46  
% 0.23/0.46  tff(u41,negated_conjecture,
% 0.23/0.46      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.23/0.46  
% 0.23/0.46  % (831)# SZS output end Saturation.
% 0.23/0.46  % (831)------------------------------
% 0.23/0.46  % (831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.46  % (831)Termination reason: Satisfiable
% 0.23/0.46  
% 0.23/0.46  % (831)Memory used [KB]: 6140
% 0.23/0.46  % (831)Time elapsed: 0.031 s
% 0.23/0.46  % (831)------------------------------
% 0.23/0.46  % (831)------------------------------
% 0.23/0.47  % (812)Success in time 0.093 s
%------------------------------------------------------------------------------
