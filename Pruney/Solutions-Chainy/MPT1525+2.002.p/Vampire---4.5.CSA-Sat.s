%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:54 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   29 (  29 expanded)
%              Depth                    :    0
%              Number of atoms          :  109 ( 109 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u181,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(sK0) = X1 ) )).

tff(u180,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK0) = X0 ) )).

tff(u179,negated_conjecture,
    ( u1_struct_0(sK0) != u1_struct_0(sK1)
    | u1_struct_0(sK0) = u1_struct_0(sK1) )).

tff(u178,negated_conjecture,
    ( u1_orders_2(sK0) != u1_orders_2(sK1)
    | u1_orders_2(sK0) = u1_orders_2(sK1) )).

tff(u177,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) )).

tff(u176,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u175,negated_conjecture,
    ( ~ l1_orders_2(sK1)
    | l1_orders_2(sK1) )).

tff(u174,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) )).

tff(u173,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) )).

tff(u172,negated_conjecture,
    ( ~ ! [X0] : m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
    | ~ ! [X1,X0] :
          ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
          | r1_orders_2(sK1,X0,X1)
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ ! [X0] :
          ( ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
          | r2_hidden(k4_tarski(sK3(sK0,X0),sK3(sK0,X0)),u1_orders_2(sK0)) )
    | ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
        | r1_orders_2(sK1,sK3(sK0,X0),sK3(sK0,X0)) ) )).

tff(u171,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
          | r2_hidden(k4_tarski(sK3(sK0,X0),sK3(sK0,X0)),u1_orders_2(sK0)) )
    | ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
        | r2_hidden(k4_tarski(sK3(sK0,X0),sK3(sK0,X0)),u1_orders_2(sK0)) ) )).

tff(u170,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
          | r1_orders_2(sK0,sK3(sK0,X0),sK3(sK0,X0)) )
    | ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3(sK0,X0),sK3(sK0,X0)) ) )).

tff(u169,negated_conjecture,
    ( ~ ! [X0] : m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
    | ! [X0] : m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) )).

tff(u168,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u167,axiom,(
    ! [X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK4(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,sK2(X0),X2)
      | ~ l1_orders_2(X0)
      | v3_lattice3(X0) ) )).

tff(u166,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u165,negated_conjecture,
    ( ~ ! [X0] : m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
    | ~ ! [X0] :
          ( ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
          | r1_orders_2(sK0,sK3(sK0,X0),sK3(sK0,X0)) )
    | ! [X0] : r1_orders_2(sK0,sK3(sK0,X0),sK3(sK0,X0)) )).

tff(u164,negated_conjecture,
    ( ~ ! [X0] : m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
    | ~ ! [X1,X0] :
          ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
          | r1_orders_2(sK1,X0,X1)
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ ! [X0] :
          ( ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
          | r2_hidden(k4_tarski(sK3(sK0,X0),sK3(sK0,X0)),u1_orders_2(sK0)) )
    | ! [X0] : r1_orders_2(sK1,sK3(sK0,X0),sK3(sK0,X0)) )).

tff(u163,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) )).

tff(u162,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
          | r1_orders_2(sK1,X0,X1)
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) )).

tff(u161,negated_conjecture,
    ( ~ ! [X0] : m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
    | ~ ! [X0] :
          ( ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
          | r2_hidden(k4_tarski(sK3(sK0,X0),sK3(sK0,X0)),u1_orders_2(sK0)) )
    | ! [X0] : r2_hidden(k4_tarski(sK3(sK0,X0),sK3(sK0,X0)),u1_orders_2(sK0)) )).

tff(u160,negated_conjecture,
    ( ~ ~ v3_lattice3(sK1)
    | ~ v3_lattice3(sK1) )).

tff(u159,axiom,(
    ! [X1,X0] :
      ( ~ v3_lattice3(X0)
      | r2_lattice3(X0,X1,sK3(X0,X1))
      | ~ l1_orders_2(X0) ) )).

tff(u158,axiom,(
    ! [X1,X0] :
      ( ~ v3_lattice3(X0)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u157,negated_conjecture,
    ( ~ v3_lattice3(sK0)
    | v3_lattice3(sK0) )).

tff(u156,axiom,(
    ! [X1,X3,X0] :
      ( ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,sK3(X0,X1),X3)
      | ~ v3_lattice3(X0) ) )).

tff(u155,axiom,(
    ! [X0,X2] :
      ( ~ r2_lattice3(X0,sK2(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,sK2(X0),sK4(X0,X2))
      | v3_lattice3(X0) ) )).

tff(u154,axiom,(
    ! [X0,X2] :
      ( ~ r2_lattice3(X0,sK2(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK4(X0,X2),u1_struct_0(X0))
      | v3_lattice3(X0) ) )).

tff(u153,negated_conjecture,
    ( ~ ! [X0] : r2_lattice3(sK0,X0,sK3(sK0,X0))
    | ! [X0] : r2_lattice3(sK0,X0,sK3(sK0,X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.48  % (12925)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.49  % (12925)Refutation not found, incomplete strategy% (12925)------------------------------
% 0.22/0.49  % (12925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (12925)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (12925)Memory used [KB]: 10618
% 0.22/0.49  % (12925)Time elapsed: 0.070 s
% 0.22/0.49  % (12925)------------------------------
% 0.22/0.49  % (12925)------------------------------
% 0.22/0.49  % (12933)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.50  % (12933)Refutation not found, incomplete strategy% (12933)------------------------------
% 0.22/0.50  % (12933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (12933)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (12933)Memory used [KB]: 10746
% 0.22/0.50  % (12933)Time elapsed: 0.084 s
% 0.22/0.50  % (12933)------------------------------
% 0.22/0.50  % (12933)------------------------------
% 0.22/0.50  % (12943)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.52  % (12921)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (12919)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (12919)Refutation not found, incomplete strategy% (12919)------------------------------
% 0.22/0.52  % (12919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12919)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12919)Memory used [KB]: 6268
% 0.22/0.52  % (12919)Time elapsed: 0.074 s
% 0.22/0.52  % (12919)------------------------------
% 0.22/0.52  % (12919)------------------------------
% 0.22/0.52  % (12930)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (12943)Refutation not found, incomplete strategy% (12943)------------------------------
% 0.22/0.52  % (12943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12943)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12943)Memory used [KB]: 1791
% 0.22/0.52  % (12943)Time elapsed: 0.058 s
% 0.22/0.52  % (12943)------------------------------
% 0.22/0.52  % (12943)------------------------------
% 0.22/0.52  % (12927)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (12917)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (12922)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (12938)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (12916)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (12938)Refutation not found, incomplete strategy% (12938)------------------------------
% 0.22/0.53  % (12938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12935)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (12938)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12938)Memory used [KB]: 6268
% 0.22/0.54  % (12938)Time elapsed: 0.120 s
% 0.22/0.54  % (12938)------------------------------
% 0.22/0.54  % (12938)------------------------------
% 0.22/0.54  % (12914)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (12941)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (12914)Refutation not found, incomplete strategy% (12914)------------------------------
% 0.22/0.54  % (12914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12914)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12914)Memory used [KB]: 1663
% 0.22/0.54  % (12914)Time elapsed: 0.127 s
% 0.22/0.54  % (12914)------------------------------
% 0.22/0.54  % (12914)------------------------------
% 0.22/0.54  % (12935)Refutation not found, incomplete strategy% (12935)------------------------------
% 0.22/0.54  % (12935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12935)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12935)Memory used [KB]: 1791
% 0.22/0.54  % (12935)Time elapsed: 0.128 s
% 0.22/0.54  % (12935)------------------------------
% 0.22/0.54  % (12935)------------------------------
% 0.22/0.54  % (12921)Refutation not found, incomplete strategy% (12921)------------------------------
% 0.22/0.54  % (12921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12921)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12921)Memory used [KB]: 6268
% 0.22/0.54  % (12921)Time elapsed: 0.110 s
% 0.22/0.54  % (12921)------------------------------
% 0.22/0.54  % (12921)------------------------------
% 0.22/0.54  % (12922)Refutation not found, incomplete strategy% (12922)------------------------------
% 0.22/0.54  % (12922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12922)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12922)Memory used [KB]: 10746
% 0.22/0.54  % (12922)Time elapsed: 0.131 s
% 0.22/0.54  % (12922)------------------------------
% 0.22/0.54  % (12922)------------------------------
% 0.22/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.54  % (12930)# SZS output start Saturation.
% 0.22/0.54  tff(u181,negated_conjecture,
% 0.22/0.54      ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | (![X1, X0] : (((g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | (u1_orders_2(sK0) = X1)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u180,negated_conjecture,
% 0.22/0.54      ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | (![X1, X0] : (((g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | (u1_struct_0(sK0) = X0)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u179,negated_conjecture,
% 0.22/0.54      ((~(u1_struct_0(sK0) = u1_struct_0(sK1))) | (u1_struct_0(sK0) = u1_struct_0(sK1)))).
% 0.22/0.54  
% 0.22/0.54  tff(u178,negated_conjecture,
% 0.22/0.54      ((~(u1_orders_2(sK0) = u1_orders_2(sK1))) | (u1_orders_2(sK0) = u1_orders_2(sK1)))).
% 0.22/0.54  
% 0.22/0.54  tff(u177,axiom,
% 0.22/0.54      (![X0] : ((~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))))).
% 0.22/0.54  
% 0.22/0.54  tff(u176,negated_conjecture,
% 0.22/0.54      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.22/0.54  
% 0.22/0.54  tff(u175,negated_conjecture,
% 0.22/0.54      ((~l1_orders_2(sK1)) | l1_orders_2(sK1))).
% 0.22/0.54  
% 0.22/0.54  tff(u174,axiom,
% 0.22/0.54      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X1 = X3))))).
% 0.22/0.54  
% 0.22/0.54  tff(u173,axiom,
% 0.22/0.54      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X0 = X2))))).
% 0.22/0.54  
% 0.22/0.54  tff(u172,negated_conjecture,
% 0.22/0.54      ((~(![X0] : (m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))))) | (~(![X1, X0] : ((~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | r1_orders_2(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))))) | (~(![X0] : ((~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) | r2_hidden(k4_tarski(sK3(sK0,X0),sK3(sK0,X0)),u1_orders_2(sK0)))))) | (![X0] : ((~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) | r1_orders_2(sK1,sK3(sK0,X0),sK3(sK0,X0))))))).
% 0.22/0.54  
% 0.22/0.54  tff(u171,negated_conjecture,
% 0.22/0.54      ((~(![X0] : ((~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) | r2_hidden(k4_tarski(sK3(sK0,X0),sK3(sK0,X0)),u1_orders_2(sK0)))))) | (![X0] : ((~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) | r2_hidden(k4_tarski(sK3(sK0,X0),sK3(sK0,X0)),u1_orders_2(sK0))))))).
% 0.22/0.54  
% 0.22/0.54  tff(u170,negated_conjecture,
% 0.22/0.54      ((~(![X0] : ((~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(sK0,X0),sK3(sK0,X0)))))) | (![X0] : ((~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(sK0,X0),sK3(sK0,X0))))))).
% 0.22/0.54  
% 0.22/0.54  tff(u169,negated_conjecture,
% 0.22/0.54      ((~(![X0] : (m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))))) | (![X0] : (m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u168,negated_conjecture,
% 0.22/0.54      ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u167,axiom,
% 0.22/0.54      (![X0, X2] : ((~r1_orders_2(X0,X2,sK4(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_lattice3(X0,sK2(X0),X2) | ~l1_orders_2(X0) | v3_lattice3(X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u166,axiom,
% 0.22/0.54      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u165,negated_conjecture,
% 0.22/0.54      ((~(![X0] : (m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))))) | (~(![X0] : ((~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(sK0,X0),sK3(sK0,X0)))))) | (![X0] : (r1_orders_2(sK0,sK3(sK0,X0),sK3(sK0,X0)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u164,negated_conjecture,
% 0.22/0.54      ((~(![X0] : (m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))))) | (~(![X1, X0] : ((~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | r1_orders_2(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))))) | (~(![X0] : ((~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) | r2_hidden(k4_tarski(sK3(sK0,X0),sK3(sK0,X0)),u1_orders_2(sK0)))))) | (![X0] : (r1_orders_2(sK1,sK3(sK0,X0),sK3(sK0,X0)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u163,axiom,
% 0.22/0.54      (![X1, X0, X2] : ((~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2))))).
% 0.22/0.54  
% 0.22/0.54  tff(u162,negated_conjecture,
% 0.22/0.54      ((~(![X1, X0] : ((~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | r1_orders_2(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))))) | (![X1, X0] : ((~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | r1_orders_2(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))))))).
% 0.22/0.54  
% 0.22/0.54  tff(u161,negated_conjecture,
% 0.22/0.54      ((~(![X0] : (m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))))) | (~(![X0] : ((~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) | r2_hidden(k4_tarski(sK3(sK0,X0),sK3(sK0,X0)),u1_orders_2(sK0)))))) | (![X0] : (r2_hidden(k4_tarski(sK3(sK0,X0),sK3(sK0,X0)),u1_orders_2(sK0)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u160,negated_conjecture,
% 0.22/0.54      ((~~v3_lattice3(sK1)) | ~v3_lattice3(sK1))).
% 0.22/0.54  
% 0.22/0.54  tff(u159,axiom,
% 0.22/0.54      (![X1, X0] : ((~v3_lattice3(X0) | r2_lattice3(X0,X1,sK3(X0,X1)) | ~l1_orders_2(X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u158,axiom,
% 0.22/0.54      (![X1, X0] : ((~v3_lattice3(X0) | m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u157,negated_conjecture,
% 0.22/0.54      ((~v3_lattice3(sK0)) | v3_lattice3(sK0))).
% 0.22/0.54  
% 0.22/0.54  tff(u156,axiom,
% 0.22/0.54      (![X1, X3, X0] : ((~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,sK3(X0,X1),X3) | ~v3_lattice3(X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u155,axiom,
% 0.22/0.54      (![X0, X2] : ((~r2_lattice3(X0,sK2(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,sK2(X0),sK4(X0,X2)) | v3_lattice3(X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u154,axiom,
% 0.22/0.54      (![X0, X2] : ((~r2_lattice3(X0,sK2(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(sK4(X0,X2),u1_struct_0(X0)) | v3_lattice3(X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u153,negated_conjecture,
% 0.22/0.54      ((~(![X0] : (r2_lattice3(sK0,X0,sK3(sK0,X0))))) | (![X0] : (r2_lattice3(sK0,X0,sK3(sK0,X0)))))).
% 0.22/0.54  
% 0.22/0.54  % (12930)# SZS output end Saturation.
% 0.22/0.54  % (12930)------------------------------
% 0.22/0.54  % (12930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12930)Termination reason: Satisfiable
% 0.22/0.54  
% 0.22/0.54  % (12930)Memory used [KB]: 10746
% 0.22/0.54  % (12930)Time elapsed: 0.131 s
% 0.22/0.54  % (12930)------------------------------
% 0.22/0.54  % (12930)------------------------------
% 0.22/0.54  % (12913)Success in time 0.177 s
%------------------------------------------------------------------------------
