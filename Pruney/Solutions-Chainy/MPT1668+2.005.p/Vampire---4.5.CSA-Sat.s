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
% DateTime   : Thu Dec  3 13:17:15 EST 2020

% Result     : CounterSatisfiable 1.45s
% Output     : Saturation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    0
%              Number of atoms          :   43 (  43 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u90,negated_conjecture,
    ( sK1 != k5_waybel_0(sK0,sK2)
    | sK1 = k5_waybel_0(sK0,sK2) )).

tff(u89,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u88,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | v3_orders_2(sK0) )).

tff(u87,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u86,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) )).

tff(u85,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) )).

tff(u84,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) )).

tff(u83,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r1_orders_2(X0,X1,X1) ) )).

tff(u82,negated_conjecture,
    ( ~ ! [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK0))
          | sK1 != k5_waybel_0(sK0,X2) )
    | ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK1 != k5_waybel_0(sK0,X2) ) )).

tff(u81,negated_conjecture,
    ( ~ ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u80,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u79,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) )).

tff(u78,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,sK2)
    | r1_orders_2(sK0,sK2,sK2) )).

tff(u77,negated_conjecture,
    ( ~ v14_waybel_0(sK1,sK0)
    | v14_waybel_0(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 14:44:41 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.52  % (10678)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (10675)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (10694)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (10683)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (10683)Refutation not found, incomplete strategy% (10683)------------------------------
% 0.22/0.53  % (10683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10683)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (10683)Memory used [KB]: 6140
% 0.22/0.53  % (10683)Time elapsed: 0.092 s
% 0.22/0.53  % (10683)------------------------------
% 0.22/0.53  % (10683)------------------------------
% 0.22/0.53  % (10686)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (10675)Refutation not found, incomplete strategy% (10675)------------------------------
% 0.22/0.53  % (10675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10675)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (10675)Memory used [KB]: 6268
% 0.22/0.53  % (10675)Time elapsed: 0.105 s
% 0.22/0.53  % (10675)------------------------------
% 0.22/0.53  % (10675)------------------------------
% 1.24/0.53  % (10678)Refutation not found, incomplete strategy% (10678)------------------------------
% 1.24/0.53  % (10678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (10678)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (10678)Memory used [KB]: 6268
% 1.24/0.53  % (10678)Time elapsed: 0.102 s
% 1.24/0.53  % (10678)------------------------------
% 1.24/0.53  % (10678)------------------------------
% 1.24/0.54  % (10686)Refutation not found, incomplete strategy% (10686)------------------------------
% 1.24/0.54  % (10686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (10686)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (10682)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.24/0.54  % (10686)Memory used [KB]: 6140
% 1.24/0.54  % (10686)Time elapsed: 0.003 s
% 1.24/0.54  % (10686)------------------------------
% 1.24/0.54  % (10686)------------------------------
% 1.24/0.54  % (10691)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.24/0.54  % (10691)Refutation not found, incomplete strategy% (10691)------------------------------
% 1.24/0.54  % (10691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (10691)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (10691)Memory used [KB]: 10746
% 1.24/0.54  % (10691)Time elapsed: 0.103 s
% 1.24/0.54  % (10691)------------------------------
% 1.24/0.54  % (10691)------------------------------
% 1.24/0.54  % (10676)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.24/0.54  % (10671)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.24/0.54  % (10676)Refutation not found, incomplete strategy% (10676)------------------------------
% 1.24/0.54  % (10676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (10676)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (10676)Memory used [KB]: 6140
% 1.24/0.54  % (10676)Time elapsed: 0.117 s
% 1.24/0.54  % (10676)------------------------------
% 1.24/0.54  % (10676)------------------------------
% 1.24/0.54  % (10671)Refutation not found, incomplete strategy% (10671)------------------------------
% 1.24/0.54  % (10671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (10671)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (10671)Memory used [KB]: 1663
% 1.24/0.54  % (10671)Time elapsed: 0.116 s
% 1.24/0.54  % (10671)------------------------------
% 1.24/0.54  % (10671)------------------------------
% 1.24/0.55  % (10684)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.24/0.55  % (10695)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.24/0.55  % (10672)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.45/0.56  % (10674)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.45/0.56  % (10674)Refutation not found, incomplete strategy% (10674)------------------------------
% 1.45/0.56  % (10674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (10674)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (10674)Memory used [KB]: 10746
% 1.45/0.56  % (10674)Time elapsed: 0.126 s
% 1.45/0.56  % (10674)------------------------------
% 1.45/0.56  % (10674)------------------------------
% 1.45/0.56  % (10699)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.45/0.56  % (10682)Refutation not found, incomplete strategy% (10682)------------------------------
% 1.45/0.56  % (10682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (10682)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (10682)Memory used [KB]: 10618
% 1.45/0.56  % (10682)Time elapsed: 0.124 s
% 1.45/0.56  % (10682)------------------------------
% 1.45/0.56  % (10682)------------------------------
% 1.45/0.56  % (10696)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.45/0.56  % (10692)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.56  % (10692)Refutation not found, incomplete strategy% (10692)------------------------------
% 1.45/0.56  % (10692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (10692)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (10692)Memory used [KB]: 1663
% 1.45/0.56  % (10692)Time elapsed: 0.141 s
% 1.45/0.56  % (10692)------------------------------
% 1.45/0.56  % (10692)------------------------------
% 1.45/0.56  % (10696)Refutation not found, incomplete strategy% (10696)------------------------------
% 1.45/0.56  % (10696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (10696)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (10696)Memory used [KB]: 6268
% 1.45/0.56  % (10696)Time elapsed: 0.138 s
% 1.45/0.56  % (10696)------------------------------
% 1.45/0.56  % (10696)------------------------------
% 1.45/0.56  % (10687)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.56  % (10690)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.45/0.57  % (10700)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.45/0.57  % (10688)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.57  % (10681)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.57  % (10690)Refutation not found, incomplete strategy% (10690)------------------------------
% 1.45/0.57  % (10690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (10690)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (10690)Memory used [KB]: 10746
% 1.45/0.57  % (10690)Time elapsed: 0.141 s
% 1.45/0.57  % (10690)------------------------------
% 1.45/0.57  % (10690)------------------------------
% 1.45/0.57  % (10700)Refutation not found, incomplete strategy% (10700)------------------------------
% 1.45/0.57  % (10700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (10700)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (10700)Memory used [KB]: 1663
% 1.45/0.57  % (10700)Time elapsed: 0.102 s
% 1.45/0.57  % (10700)------------------------------
% 1.45/0.57  % (10700)------------------------------
% 1.45/0.57  % SZS status CounterSatisfiable for theBenchmark
% 1.45/0.57  % (10687)# SZS output start Saturation.
% 1.45/0.57  tff(u90,negated_conjecture,
% 1.45/0.57      ((~(sK1 = k5_waybel_0(sK0,sK2))) | (sK1 = k5_waybel_0(sK0,sK2)))).
% 1.45/0.57  
% 1.45/0.57  tff(u89,negated_conjecture,
% 1.45/0.57      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 1.45/0.57  
% 1.45/0.57  tff(u88,negated_conjecture,
% 1.45/0.57      ((~v3_orders_2(sK0)) | v3_orders_2(sK0))).
% 1.45/0.57  
% 1.45/0.57  tff(u87,negated_conjecture,
% 1.45/0.57      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 1.45/0.57  
% 1.45/0.57  tff(u86,axiom,
% 1.45/0.57      (![X1, X3, X0, X2] : ((~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X3,X2) | ~r2_lattice3(X0,X1,X2))))).
% 1.45/0.57  
% 1.45/0.57  tff(u85,axiom,
% 1.45/0.57      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2))))).
% 1.45/0.57  
% 1.45/0.57  tff(u84,axiom,
% 1.45/0.57      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(sK3(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2))))).
% 1.45/0.57  
% 1.45/0.57  tff(u83,axiom,
% 1.45/0.57      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r1_orders_2(X0,X1,X1))))).
% 1.45/0.57  
% 1.45/0.57  tff(u82,negated_conjecture,
% 1.45/0.57      ((~(![X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | (sK1 != k5_waybel_0(sK0,X2)))))) | (![X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | (sK1 != k5_waybel_0(sK0,X2))))))).
% 1.45/0.57  
% 1.45/0.57  tff(u81,negated_conjecture,
% 1.45/0.57      ((~~m1_subset_1(sK2,u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)))).
% 1.45/0.57  
% 1.45/0.57  tff(u80,negated_conjecture,
% 1.45/0.57      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.45/0.57  
% 1.45/0.57  tff(u79,axiom,
% 1.45/0.57      (![X1, X0, X2] : ((~r1_orders_2(X0,sK3(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2))))).
% 1.45/0.57  
% 1.45/0.57  tff(u78,negated_conjecture,
% 1.45/0.57      ((~r1_orders_2(sK0,sK2,sK2)) | r1_orders_2(sK0,sK2,sK2))).
% 1.45/0.57  
% 1.45/0.57  tff(u77,negated_conjecture,
% 1.45/0.57      ((~v14_waybel_0(sK1,sK0)) | v14_waybel_0(sK1,sK0))).
% 1.45/0.57  
% 1.45/0.57  % (10687)# SZS output end Saturation.
% 1.45/0.57  % (10687)------------------------------
% 1.45/0.57  % (10687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (10687)Termination reason: Satisfiable
% 1.45/0.57  
% 1.45/0.57  % (10687)Memory used [KB]: 10746
% 1.45/0.57  % (10687)Time elapsed: 0.139 s
% 1.45/0.57  % (10687)------------------------------
% 1.45/0.57  % (10687)------------------------------
% 1.45/0.57  % (10688)Refutation not found, incomplete strategy% (10688)------------------------------
% 1.45/0.57  % (10688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (10688)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (10688)Memory used [KB]: 10618
% 1.45/0.57  % (10688)Time elapsed: 0.138 s
% 1.45/0.57  % (10688)------------------------------
% 1.45/0.57  % (10688)------------------------------
% 1.45/0.57  % (10670)Success in time 0.185 s
%------------------------------------------------------------------------------
