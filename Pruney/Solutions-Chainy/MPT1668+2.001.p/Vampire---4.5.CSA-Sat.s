%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:14 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    0
%              Number of atoms          :   58 (  58 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u138,negated_conjecture,
    ( ~ ( u1_struct_0(sK0) != sK1 )
    | u1_struct_0(sK0) != sK1 )).

tff(u137,negated_conjecture,
    ( sK1 != k5_waybel_0(sK0,sK2)
    | sK1 = k5_waybel_0(sK0,sK2) )).

tff(u136,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) )).

tff(u135,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) )).

tff(u134,negated_conjecture,
    ( ~ ~ r1_tarski(u1_struct_0(sK0),sK1)
    | ~ r1_tarski(u1_struct_0(sK0),sK1) )).

tff(u133,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u132,negated_conjecture,(
    r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u131,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u130,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u129,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u128,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u127,negated_conjecture,
    ( ~ ! [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK0))
          | k5_waybel_0(sK0,X2) != sK1 )
    | ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k5_waybel_0(sK0,X2) != sK1 ) )).

tff(u126,negated_conjecture,
    ( ~ ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u125,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u124,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u123,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r2_hidden(X4,X1)
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u122,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) )).

tff(u121,negated_conjecture,
    ( ~ ~ r2_hidden(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r2_hidden(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) )).

tff(u120,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u119,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u118,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u117,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u116,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK1,sK2)
    | ~ r2_lattice3(sK0,sK1,sK2) )).

tff(u115,negated_conjecture,
    ( ~ v14_waybel_0(sK1,sK0)
    | v14_waybel_0(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.44  % (7428)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.46  % (7420)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.48  % (7420)Refutation not found, incomplete strategy% (7420)------------------------------
% 0.22/0.48  % (7420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (7420)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (7420)Memory used [KB]: 10618
% 0.22/0.49  % (7420)Time elapsed: 0.081 s
% 0.22/0.49  % (7420)------------------------------
% 0.22/0.49  % (7420)------------------------------
% 0.22/0.49  % (7441)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.50  % (7425)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (7443)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (7442)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (7422)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (7439)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (7445)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.51  % (7425)Refutation not found, incomplete strategy% (7425)------------------------------
% 0.22/0.51  % (7425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (7425)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (7425)Memory used [KB]: 6140
% 0.22/0.51  % (7425)Time elapsed: 0.094 s
% 0.22/0.51  % (7425)------------------------------
% 0.22/0.51  % (7425)------------------------------
% 0.22/0.51  % (7424)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (7435)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (7424)Refutation not found, incomplete strategy% (7424)------------------------------
% 0.22/0.51  % (7424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (7424)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (7424)Memory used [KB]: 6140
% 0.22/0.51  % (7424)Time elapsed: 0.092 s
% 0.22/0.51  % (7424)------------------------------
% 0.22/0.51  % (7424)------------------------------
% 0.22/0.51  % (7426)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (7423)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (7435)Refutation not found, incomplete strategy% (7435)------------------------------
% 0.22/0.51  % (7435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (7426)Refutation not found, incomplete strategy% (7426)------------------------------
% 0.22/0.51  % (7426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (7427)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (7435)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (7435)Memory used [KB]: 6140
% 0.22/0.51  % (7435)Time elapsed: 0.058 s
% 0.22/0.51  % (7435)------------------------------
% 0.22/0.51  % (7435)------------------------------
% 0.22/0.51  % (7433)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (7433)Refutation not found, incomplete strategy% (7433)------------------------------
% 0.22/0.52  % (7433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7433)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (7433)Memory used [KB]: 6140
% 0.22/0.52  % (7433)Time elapsed: 0.105 s
% 0.22/0.52  % (7433)------------------------------
% 0.22/0.52  % (7433)------------------------------
% 0.22/0.52  % (7427)Refutation not found, incomplete strategy% (7427)------------------------------
% 0.22/0.52  % (7427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7427)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (7427)Memory used [KB]: 1663
% 0.22/0.52  % (7427)Time elapsed: 0.074 s
% 0.22/0.52  % (7427)------------------------------
% 0.22/0.52  % (7427)------------------------------
% 0.22/0.52  % (7431)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (7434)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (7431)Refutation not found, incomplete strategy% (7431)------------------------------
% 0.22/0.52  % (7431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7431)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (7431)Memory used [KB]: 10618
% 0.22/0.52  % (7431)Time elapsed: 0.105 s
% 0.22/0.52  % (7431)------------------------------
% 0.22/0.52  % (7431)------------------------------
% 0.22/0.52  % (7429)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (7426)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (7426)Memory used [KB]: 10618
% 0.22/0.52  % (7426)Time elapsed: 0.095 s
% 0.22/0.52  % (7426)------------------------------
% 0.22/0.52  % (7426)------------------------------
% 0.22/0.52  % (7430)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (7436)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.52  % (7430)# SZS output start Saturation.
% 0.22/0.52  tff(u138,negated_conjecture,
% 0.22/0.52      ((~(u1_struct_0(sK0) != sK1)) | (u1_struct_0(sK0) != sK1))).
% 0.22/0.52  
% 0.22/0.52  tff(u137,negated_conjecture,
% 0.22/0.52      ((~(sK1 = k5_waybel_0(sK0,sK2))) | (sK1 = k5_waybel_0(sK0,sK2)))).
% 0.22/0.52  
% 0.22/0.52  tff(u136,axiom,
% 0.22/0.52      (![X1, X0] : ((~r1_tarski(X1,X0) | (X0 = X1) | ~r1_tarski(X0,X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u135,axiom,
% 0.22/0.52      (![X1, X0] : ((~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u134,negated_conjecture,
% 0.22/0.52      ((~~r1_tarski(u1_struct_0(sK0),sK1)) | ~r1_tarski(u1_struct_0(sK0),sK1))).
% 0.22/0.52  
% 0.22/0.52  tff(u133,axiom,
% 0.22/0.52      (![X1] : (r1_tarski(X1,X1)))).
% 0.22/0.52  
% 0.22/0.52  tff(u132,negated_conjecture,
% 0.22/0.52      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.22/0.52  
% 0.22/0.52  tff(u131,axiom,
% 0.22/0.52      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u130,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u129,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK3(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u128,axiom,
% 0.22/0.52      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u127,negated_conjecture,
% 0.22/0.52      ((~(![X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | (k5_waybel_0(sK0,X2) != sK1))))) | (![X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | (k5_waybel_0(sK0,X2) != sK1)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u126,negated_conjecture,
% 0.22/0.52      ((~~m1_subset_1(sK2,u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)))).
% 0.22/0.52  
% 0.22/0.52  tff(u125,axiom,
% 0.22/0.52      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u124,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.52  
% 0.22/0.52  tff(u123,axiom,
% 0.22/0.52      (![X1, X0, X2, X4] : ((~r2_hidden(X4,X1) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u122,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u121,negated_conjecture,
% 0.22/0.52      ((~~r2_hidden(sK3(sK0,sK1,sK2),u1_struct_0(sK0))) | ~r2_hidden(sK3(sK0,sK1,sK2),u1_struct_0(sK0)))).
% 0.22/0.52  
% 0.22/0.52  tff(u120,negated_conjecture,
% 0.22/0.52      ~v2_struct_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u119,negated_conjecture,
% 0.22/0.52      v3_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u118,negated_conjecture,
% 0.22/0.52      l1_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u117,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~r1_orders_2(X0,sK3(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u116,negated_conjecture,
% 0.22/0.52      ((~~r2_lattice3(sK0,sK1,sK2)) | ~r2_lattice3(sK0,sK1,sK2))).
% 0.22/0.52  
% 0.22/0.52  tff(u115,negated_conjecture,
% 0.22/0.52      ((~v14_waybel_0(sK1,sK0)) | v14_waybel_0(sK1,sK0))).
% 0.22/0.52  
% 0.22/0.52  % (7430)# SZS output end Saturation.
% 0.22/0.52  % (7430)------------------------------
% 0.22/0.52  % (7430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7430)Termination reason: Satisfiable
% 0.22/0.52  
% 0.22/0.52  % (7430)Memory used [KB]: 10618
% 0.22/0.52  % (7430)Time elapsed: 0.104 s
% 0.22/0.52  % (7430)------------------------------
% 0.22/0.52  % (7430)------------------------------
% 0.22/0.53  % (7419)Success in time 0.167 s
%------------------------------------------------------------------------------
