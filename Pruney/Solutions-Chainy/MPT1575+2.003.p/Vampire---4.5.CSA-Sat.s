%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:20 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    0
%              Number of atoms          :   84 (  84 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u139,axiom,
    ( ~ ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

tff(u138,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ r1_tarski(X0,u1_struct_0(sK0))
          | r1_yellow_0(sK0,X0) )
    | ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | r1_yellow_0(sK0,X0) ) )).

tff(u137,axiom,
    ( ~ ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) )).

tff(u136,axiom,
    ( ~ ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0) )).

tff(u135,axiom,
    ( ~ ! [X1,X0] :
          ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
          | r1_tarski(X0,X1) )
    | ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) ) )).

tff(u134,negated_conjecture,
    ( ~ ! [X1] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          | r1_yellow_0(sK0,X1) )
    | ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_yellow_0(sK0,X1) ) )).

tff(u133,axiom,
    ( ~ ! [X1,X0] :
          ( m1_subset_1(X0,k1_zfmisc_1(X1))
          | ~ r1_tarski(X0,X1) )
    | ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) )).

tff(u132,axiom,
    ( ~ ! [X0,X4] :
          ( m1_subset_1(sK3(X0,X4),u1_struct_0(X0))
          | ~ v3_lattice3(X0)
          | ~ l1_orders_2(X0) )
    | ! [X0,X4] :
        ( m1_subset_1(sK3(X0,X4),u1_struct_0(X0))
        | ~ v3_lattice3(X0)
        | ~ l1_orders_2(X0) ) )).

tff(u131,axiom,
    ( ~ ! [X0,X2] :
          ( m1_subset_1(sK2(X0,X2),u1_struct_0(X0))
          | v3_lattice3(X0)
          | ~ r2_lattice3(X0,sK1(X0),X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0))
          | ~ l1_orders_2(X0) )
    | ! [X0,X2] :
        ( m1_subset_1(sK2(X0,X2),u1_struct_0(X0))
        | v3_lattice3(X0)
        | ~ r2_lattice3(X0,sK1(X0),X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_orders_2(X0) ) )).

tff(u130,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u129,negated_conjecture,
    ( ~ ~ v3_lattice3(sK0)
    | ~ v3_lattice3(sK0) )).

tff(u128,axiom,
    ( ~ ! [X0,X4,X6] :
          ( ~ v3_lattice3(X0)
          | ~ r2_lattice3(X0,X4,X6)
          | ~ m1_subset_1(X6,u1_struct_0(X0))
          | r1_orders_2(X0,sK3(X0,X4),X6)
          | ~ l1_orders_2(X0) )
    | ! [X0,X4,X6] :
        ( ~ v3_lattice3(X0)
        | ~ r2_lattice3(X0,X4,X6)
        | ~ m1_subset_1(X6,u1_struct_0(X0))
        | r1_orders_2(X0,sK3(X0,X4),X6)
        | ~ l1_orders_2(X0) ) )).

tff(u127,axiom,
    ( ~ ! [X0,X4] :
          ( ~ v3_lattice3(X0)
          | r2_lattice3(X0,X4,sK3(X0,X4))
          | ~ l1_orders_2(X0) )
    | ! [X0,X4] :
        ( ~ v3_lattice3(X0)
        | r2_lattice3(X0,X4,sK3(X0,X4))
        | ~ l1_orders_2(X0) ) )).

tff(u126,axiom,
    ( ~ ! [X0,X2] :
          ( r2_lattice3(X0,sK1(X0),sK2(X0,X2))
          | v3_lattice3(X0)
          | ~ r2_lattice3(X0,sK1(X0),X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0))
          | ~ l1_orders_2(X0) )
    | ! [X0,X2] :
        ( r2_lattice3(X0,sK1(X0),sK2(X0,X2))
        | v3_lattice3(X0)
        | ~ r2_lattice3(X0,sK1(X0),X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_orders_2(X0) ) )).

tff(u125,axiom,
    ( ~ ! [X0,X2] :
          ( ~ r1_orders_2(X0,X2,sK2(X0,X2))
          | v3_lattice3(X0)
          | ~ r2_lattice3(X0,sK1(X0),X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0))
          | ~ l1_orders_2(X0) )
    | ! [X0,X2] :
        ( ~ r1_orders_2(X0,X2,sK2(X0,X2))
        | v3_lattice3(X0)
        | ~ r2_lattice3(X0,sK1(X0),X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_orders_2(X0) ) )).

tff(u124,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u123,negated_conjecture,
    ( ~ ! [X0] : r1_yellow_0(sK0,k3_xboole_0(u1_struct_0(sK0),X0))
    | ! [X0] : r1_yellow_0(sK0,k3_xboole_0(u1_struct_0(sK0),X0)) )).

tff(u122,negated_conjecture,
    ( ~ ! [X1] : r1_yellow_0(sK0,k3_xboole_0(X1,u1_struct_0(sK0)))
    | ! [X1] : r1_yellow_0(sK0,k3_xboole_0(X1,u1_struct_0(sK0))) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:13:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (30002)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.44  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.44  % (30002)# SZS output start Saturation.
% 0.21/0.44  tff(u139,axiom,
% 0.21/0.44      ((~(![X1, X0] : ((k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0))))) | (![X1, X0] : ((k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)))))).
% 0.21/0.44  
% 0.21/0.44  tff(u138,negated_conjecture,
% 0.21/0.44      ((~(![X0] : ((~r1_tarski(X0,u1_struct_0(sK0)) | r1_yellow_0(sK0,X0))))) | (![X0] : ((~r1_tarski(X0,u1_struct_0(sK0)) | r1_yellow_0(sK0,X0)))))).
% 0.21/0.44  
% 0.21/0.44  tff(u137,axiom,
% 0.21/0.44      ((~(![X1, X0] : (r1_tarski(k3_xboole_0(X0,X1),X0)))) | (![X1, X0] : (r1_tarski(k3_xboole_0(X0,X1),X0))))).
% 0.21/0.44  
% 0.21/0.44  tff(u136,axiom,
% 0.21/0.44      ((~(![X1, X0] : (r1_tarski(k3_xboole_0(X1,X0),X0)))) | (![X1, X0] : (r1_tarski(k3_xboole_0(X1,X0),X0))))).
% 0.21/0.44  
% 0.21/0.44  tff(u135,axiom,
% 0.21/0.44      ((~(![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))) | (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)))))).
% 0.21/0.44  
% 0.21/0.44  tff(u134,negated_conjecture,
% 0.21/0.44      ((~(![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_yellow_0(sK0,X1))))) | (![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_yellow_0(sK0,X1)))))).
% 0.21/0.44  
% 0.21/0.44  tff(u133,axiom,
% 0.21/0.44      ((~(![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))))) | (![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)))))).
% 0.21/0.44  
% 0.21/0.44  tff(u132,axiom,
% 0.21/0.44      ((~(![X0, X4] : ((m1_subset_1(sK3(X0,X4),u1_struct_0(X0)) | ~v3_lattice3(X0) | ~l1_orders_2(X0))))) | (![X0, X4] : ((m1_subset_1(sK3(X0,X4),u1_struct_0(X0)) | ~v3_lattice3(X0) | ~l1_orders_2(X0)))))).
% 0.21/0.44  
% 0.21/0.44  tff(u131,axiom,
% 0.21/0.44      ((~(![X0, X2] : ((m1_subset_1(sK2(X0,X2),u1_struct_0(X0)) | v3_lattice3(X0) | ~r2_lattice3(X0,sK1(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))) | (![X0, X2] : ((m1_subset_1(sK2(X0,X2),u1_struct_0(X0)) | v3_lattice3(X0) | ~r2_lattice3(X0,sK1(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)))))).
% 0.21/0.44  
% 0.21/0.44  tff(u130,negated_conjecture,
% 0.21/0.44      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.21/0.44  
% 0.21/0.44  tff(u129,negated_conjecture,
% 0.21/0.44      ((~~v3_lattice3(sK0)) | ~v3_lattice3(sK0))).
% 0.21/0.44  
% 0.21/0.44  tff(u128,axiom,
% 0.21/0.44      ((~(![X0, X4, X6] : ((~v3_lattice3(X0) | ~r2_lattice3(X0,X4,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | r1_orders_2(X0,sK3(X0,X4),X6) | ~l1_orders_2(X0))))) | (![X0, X4, X6] : ((~v3_lattice3(X0) | ~r2_lattice3(X0,X4,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | r1_orders_2(X0,sK3(X0,X4),X6) | ~l1_orders_2(X0)))))).
% 0.21/0.44  
% 0.21/0.44  tff(u127,axiom,
% 0.21/0.44      ((~(![X0, X4] : ((~v3_lattice3(X0) | r2_lattice3(X0,X4,sK3(X0,X4)) | ~l1_orders_2(X0))))) | (![X0, X4] : ((~v3_lattice3(X0) | r2_lattice3(X0,X4,sK3(X0,X4)) | ~l1_orders_2(X0)))))).
% 0.21/0.44  
% 0.21/0.44  tff(u126,axiom,
% 0.21/0.44      ((~(![X0, X2] : ((r2_lattice3(X0,sK1(X0),sK2(X0,X2)) | v3_lattice3(X0) | ~r2_lattice3(X0,sK1(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))) | (![X0, X2] : ((r2_lattice3(X0,sK1(X0),sK2(X0,X2)) | v3_lattice3(X0) | ~r2_lattice3(X0,sK1(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)))))).
% 0.21/0.44  
% 0.21/0.44  tff(u125,axiom,
% 0.21/0.44      ((~(![X0, X2] : ((~r1_orders_2(X0,X2,sK2(X0,X2)) | v3_lattice3(X0) | ~r2_lattice3(X0,sK1(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))) | (![X0, X2] : ((~r1_orders_2(X0,X2,sK2(X0,X2)) | v3_lattice3(X0) | ~r2_lattice3(X0,sK1(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)))))).
% 0.21/0.44  
% 0.21/0.44  tff(u124,negated_conjecture,
% 0.21/0.44      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.21/0.44  
% 0.21/0.44  tff(u123,negated_conjecture,
% 0.21/0.44      ((~(![X0] : (r1_yellow_0(sK0,k3_xboole_0(u1_struct_0(sK0),X0))))) | (![X0] : (r1_yellow_0(sK0,k3_xboole_0(u1_struct_0(sK0),X0)))))).
% 0.21/0.44  
% 0.21/0.44  tff(u122,negated_conjecture,
% 0.21/0.44      ((~(![X1] : (r1_yellow_0(sK0,k3_xboole_0(X1,u1_struct_0(sK0)))))) | (![X1] : (r1_yellow_0(sK0,k3_xboole_0(X1,u1_struct_0(sK0))))))).
% 0.21/0.44  
% 0.21/0.44  % (30002)# SZS output end Saturation.
% 0.21/0.44  % (30002)------------------------------
% 0.21/0.44  % (30002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (30002)Termination reason: Satisfiable
% 0.21/0.44  
% 0.21/0.44  % (30002)Memory used [KB]: 10618
% 0.21/0.44  % (30002)Time elapsed: 0.004 s
% 0.21/0.44  % (30002)------------------------------
% 0.21/0.44  % (30002)------------------------------
% 0.21/0.44  % (29996)Success in time 0.08 s
%------------------------------------------------------------------------------
