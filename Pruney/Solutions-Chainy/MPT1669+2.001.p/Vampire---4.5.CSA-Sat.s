%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:15 EST 2020

% Result     : CounterSatisfiable 1.41s
% Output     : Saturation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    0
%              Number of atoms          :  105 ( 105 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u175,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ ! [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK0))
          | sK1 != k6_waybel_0(sK0,X2) )
    | ! [X0] :
        ( sK1 != k6_waybel_0(sK0,sK4(sK1,X0))
        | r1_tarski(sK1,X0) ) )).

tff(u174,negated_conjecture,
    ( sK1 != k6_waybel_0(sK0,sK2)
    | sK1 = k6_waybel_0(sK0,sK2) )).

tff(u173,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK4(X0,X1),X2)
      | r1_tarski(X0,X1) ) )).

tff(u172,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) )).

tff(u171,negated_conjecture,
    ( ~ ! [X6] : r1_tarski(sK1,X6)
    | ! [X2] :
        ( ~ r1_tarski(X2,sK1)
        | sK1 = X2 ) )).

tff(u170,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ ! [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK0))
          | sK1 != k6_waybel_0(sK0,X2) )
    | ! [X0] :
        ( ~ r1_tarski(k6_waybel_0(sK0,sK4(sK1,X0)),sK1)
        | ~ r1_tarski(sK1,k6_waybel_0(sK0,sK4(sK1,X0)))
        | r1_tarski(sK1,X0) ) )).

tff(u169,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u168,negated_conjecture,
    ( ~ ! [X6] : r1_tarski(sK1,X6)
    | ! [X6] : r1_tarski(sK1,X6) )).

tff(u167,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) )).

tff(u166,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) )).

tff(u165,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) )).

tff(u164,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) )).

tff(u163,negated_conjecture,
    ( ~ ! [X5,X4] :
          ( r2_hidden(sK3(sK0,X5,sK4(sK1,X4)),X5)
          | r1_lattice3(sK0,X5,sK4(sK1,X4))
          | r1_tarski(sK1,X4) )
    | ! [X5,X4] :
        ( r2_hidden(sK3(sK0,X5,sK4(sK1,X4)),X5)
        | r1_lattice3(sK0,X5,sK4(sK1,X4))
        | r1_tarski(sK1,X4) ) )).

tff(u162,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X2) ) )).

tff(u161,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) )).

tff(u160,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r3_orders_2(X0,X1,X1)
      | ~ sP5(X0) ) )).

tff(u159,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2) ) )).

tff(u158,axiom,(
    ! [X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP5(X0) ) )).

tff(u157,negated_conjecture,
    ( ~ ! [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK0))
          | sK1 != k6_waybel_0(sK0,X2) )
    | ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK1 != k6_waybel_0(sK0,X2) ) )).

tff(u156,negated_conjecture,
    ( ~ ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u155,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK4(X0,X2),X1)
      | r1_tarski(X0,X2) ) )).

tff(u154,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u153,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] :
        ( m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
        | r1_tarski(sK1,X0) ) )).

tff(u152,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u151,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | v3_orders_2(sK0) )).

tff(u150,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u149,axiom,(
    ! [X1,X0,X2] :
      ( ~ r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) )).

tff(u148,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) )).

tff(u147,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_orders_2(X0,X1,X2) ) )).

tff(u146,negated_conjecture,
    ( ~ v15_waybel_0(sK1,sK0)
    | v15_waybel_0(sK1,sK0) )).

tff(u145,negated_conjecture,
    ( ~ ~ sP5(sK0)
    | ~ sP5(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:39:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (21633)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.50  % (21640)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.50  % (21631)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (21640)Refutation not found, incomplete strategy% (21640)------------------------------
% 0.22/0.51  % (21640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21640)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21640)Memory used [KB]: 1663
% 0.22/0.51  % (21640)Time elapsed: 0.105 s
% 0.22/0.51  % (21640)------------------------------
% 0.22/0.51  % (21640)------------------------------
% 0.22/0.52  % (21625)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (21643)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (21623)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (21629)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (21624)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.28/0.53  % (21634)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.28/0.53  % (21641)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.28/0.54  % (21621)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.54  % (21621)Refutation not found, incomplete strategy% (21621)------------------------------
% 1.28/0.54  % (21621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (21621)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (21621)Memory used [KB]: 10746
% 1.28/0.54  % (21621)Time elapsed: 0.126 s
% 1.28/0.54  % (21621)------------------------------
% 1.28/0.54  % (21621)------------------------------
% 1.28/0.54  % (21649)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.54  % (21628)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.41/0.55  % (21641)Refutation not found, incomplete strategy% (21641)------------------------------
% 1.41/0.55  % (21641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (21641)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (21641)Memory used [KB]: 10746
% 1.41/0.55  % (21641)Time elapsed: 0.118 s
% 1.41/0.55  % (21641)------------------------------
% 1.41/0.55  % (21641)------------------------------
% 1.41/0.55  % (21622)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.41/0.55  % (21628)Refutation not found, incomplete strategy% (21628)------------------------------
% 1.41/0.55  % (21628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (21628)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (21628)Memory used [KB]: 10618
% 1.41/0.55  % (21628)Time elapsed: 0.125 s
% 1.41/0.55  % (21628)------------------------------
% 1.41/0.55  % (21628)------------------------------
% 1.41/0.55  % (21623)Refutation not found, incomplete strategy% (21623)------------------------------
% 1.41/0.55  % (21623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (21623)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (21623)Memory used [KB]: 6268
% 1.41/0.55  % (21623)Time elapsed: 0.126 s
% 1.41/0.55  % (21623)------------------------------
% 1.41/0.55  % (21623)------------------------------
% 1.41/0.55  % (21632)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.55  % (21629)Refutation not found, incomplete strategy% (21629)------------------------------
% 1.41/0.55  % (21629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (21629)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (21629)Memory used [KB]: 10618
% 1.41/0.55  % (21629)Time elapsed: 0.116 s
% 1.41/0.55  % (21629)------------------------------
% 1.41/0.55  % (21629)------------------------------
% 1.41/0.55  % (21639)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.55  % (21647)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.55  % (21638)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.55  % (21648)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.55  % (21619)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.41/0.55  % (21619)Refutation not found, incomplete strategy% (21619)------------------------------
% 1.41/0.55  % (21619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (21619)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (21619)Memory used [KB]: 1663
% 1.41/0.55  % (21619)Time elapsed: 0.136 s
% 1.41/0.55  % (21619)------------------------------
% 1.41/0.55  % (21619)------------------------------
% 1.41/0.55  % (21630)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.55  % (21639)Refutation not found, incomplete strategy% (21639)------------------------------
% 1.41/0.55  % (21639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (21639)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (21639)Memory used [KB]: 10746
% 1.41/0.55  % (21639)Time elapsed: 0.143 s
% 1.41/0.55  % (21639)------------------------------
% 1.41/0.55  % (21639)------------------------------
% 1.41/0.55  % (21630)Refutation not found, incomplete strategy% (21630)------------------------------
% 1.41/0.55  % (21630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (21630)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (21630)Memory used [KB]: 10618
% 1.41/0.55  % (21630)Time elapsed: 0.138 s
% 1.41/0.55  % (21630)------------------------------
% 1.41/0.55  % (21630)------------------------------
% 1.41/0.56  % (21620)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.41/0.56  % (21644)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.56  % (21637)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.56  % (21635)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.56  % (21626)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.56  % (21626)Refutation not found, incomplete strategy% (21626)------------------------------
% 1.41/0.56  % (21626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % SZS status CounterSatisfiable for theBenchmark
% 1.41/0.57  % (21626)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.57  
% 1.41/0.57  % (21626)Memory used [KB]: 6268
% 1.41/0.57  % (21626)Time elapsed: 0.153 s
% 1.41/0.57  % (21626)------------------------------
% 1.41/0.57  % (21626)------------------------------
% 1.41/0.57  % (21635)# SZS output start Saturation.
% 1.41/0.57  tff(u175,negated_conjecture,
% 1.41/0.57      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (~(![X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | (sK1 != k6_waybel_0(sK0,X2)))))) | (![X0] : (((sK1 != k6_waybel_0(sK0,sK4(sK1,X0))) | r1_tarski(sK1,X0)))))).
% 1.41/0.57  
% 1.41/0.57  tff(u174,negated_conjecture,
% 1.41/0.57      ((~(sK1 = k6_waybel_0(sK0,sK2))) | (sK1 = k6_waybel_0(sK0,sK2)))).
% 1.41/0.57  
% 1.41/0.57  tff(u173,axiom,
% 1.41/0.57      (![X1, X0, X2] : ((~r1_tarski(X0,X2) | r2_hidden(sK4(X0,X1),X2) | r1_tarski(X0,X1))))).
% 1.41/0.57  
% 1.41/0.57  tff(u172,axiom,
% 1.41/0.57      (![X1, X0] : ((~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | (X0 = X1))))).
% 1.41/0.57  
% 1.41/0.57  tff(u171,negated_conjecture,
% 1.41/0.57      ((~(![X6] : (r1_tarski(sK1,X6)))) | (![X2] : ((~r1_tarski(X2,sK1) | (sK1 = X2)))))).
% 1.41/0.57  
% 1.41/0.57  tff(u170,negated_conjecture,
% 1.41/0.57      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (~(![X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | (sK1 != k6_waybel_0(sK0,X2)))))) | (![X0] : ((~r1_tarski(k6_waybel_0(sK0,sK4(sK1,X0)),sK1) | ~r1_tarski(sK1,k6_waybel_0(sK0,sK4(sK1,X0))) | r1_tarski(sK1,X0)))))).
% 1.41/0.57  
% 1.41/0.57  tff(u169,axiom,
% 1.41/0.57      (![X1] : (r1_tarski(X1,X1)))).
% 1.41/0.57  
% 1.41/0.57  tff(u168,negated_conjecture,
% 1.41/0.57      ((~(![X6] : (r1_tarski(sK1,X6)))) | (![X6] : (r1_tarski(sK1,X6))))).
% 1.41/0.57  
% 1.41/0.57  tff(u167,axiom,
% 1.41/0.57      (![X1, X0] : ((~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1))))).
% 1.41/0.57  
% 1.41/0.57  tff(u166,axiom,
% 1.41/0.57      (![X1, X0, X2] : ((~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))))).
% 1.41/0.57  
% 1.41/0.57  tff(u165,axiom,
% 1.41/0.57      (![X1, X0, X2] : ((~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1))))).
% 1.41/0.57  
% 1.41/0.57  tff(u164,axiom,
% 1.41/0.57      (![X1, X0] : ((r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1))))).
% 1.41/0.57  
% 1.41/0.57  tff(u163,negated_conjecture,
% 1.41/0.57      ((~(![X5, X4] : ((r2_hidden(sK3(sK0,X5,sK4(sK1,X4)),X5) | r1_lattice3(sK0,X5,sK4(sK1,X4)) | r1_tarski(sK1,X4))))) | (![X5, X4] : ((r2_hidden(sK3(sK0,X5,sK4(sK1,X4)),X5) | r1_lattice3(sK0,X5,sK4(sK1,X4)) | r1_tarski(sK1,X4)))))).
% 1.41/0.57  
% 1.41/0.57  tff(u162,axiom,
% 1.41/0.57      (![X1, X3, X0, X2] : ((~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X2,X3) | ~r1_lattice3(X0,X1,X2))))).
% 1.41/0.57  
% 1.41/0.57  tff(u161,axiom,
% 1.41/0.57      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2))))).
% 1.41/0.57  
% 1.41/0.57  tff(u160,axiom,
% 1.41/0.57      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r3_orders_2(X0,X1,X1) | ~sP5(X0))))).
% 1.41/0.57  
% 1.41/0.57  tff(u159,axiom,
% 1.41/0.57      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(sK3(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2))))).
% 1.41/0.57  
% 1.41/0.57  tff(u158,axiom,
% 1.41/0.57      (![X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP5(X0))))).
% 1.41/0.57  
% 1.41/0.57  tff(u157,negated_conjecture,
% 1.41/0.57      ((~(![X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | (sK1 != k6_waybel_0(sK0,X2)))))) | (![X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | (sK1 != k6_waybel_0(sK0,X2))))))).
% 1.41/0.57  
% 1.41/0.57  tff(u156,negated_conjecture,
% 1.41/0.57      ((~~m1_subset_1(sK2,u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)))).
% 1.41/0.57  
% 1.41/0.57  tff(u155,axiom,
% 1.41/0.57      (![X1, X0, X2] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK4(X0,X2),X1) | r1_tarski(X0,X2))))).
% 1.41/0.57  
% 1.41/0.57  tff(u154,negated_conjecture,
% 1.41/0.57      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.41/0.57  
% 1.41/0.57  tff(u153,negated_conjecture,
% 1.41/0.57      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0)) | r1_tarski(sK1,X0)))))).
% 1.41/0.57  
% 1.41/0.57  tff(u152,negated_conjecture,
% 1.41/0.57      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 1.41/0.57  
% 1.41/0.57  tff(u151,negated_conjecture,
% 1.41/0.57      ((~v3_orders_2(sK0)) | v3_orders_2(sK0))).
% 1.41/0.57  
% 1.41/0.57  tff(u150,negated_conjecture,
% 1.41/0.57      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 1.41/0.57  
% 1.41/0.57  tff(u149,axiom,
% 1.41/0.57      (![X1, X0, X2] : ((~r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | v2_struct_0(X0))))).
% 1.41/0.57  
% 1.41/0.57  tff(u148,axiom,
% 1.41/0.57      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2))))).
% 1.41/0.57  
% 1.41/0.57  tff(u147,axiom,
% 1.41/0.57      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r3_orders_2(X0,X1,X2))))).
% 1.41/0.57  
% 1.41/0.57  tff(u146,negated_conjecture,
% 1.41/0.57      ((~v15_waybel_0(sK1,sK0)) | v15_waybel_0(sK1,sK0))).
% 1.41/0.57  
% 1.41/0.57  tff(u145,negated_conjecture,
% 1.41/0.57      ((~~sP5(sK0)) | ~sP5(sK0))).
% 1.41/0.57  
% 1.41/0.57  % (21635)# SZS output end Saturation.
% 1.41/0.57  % (21635)------------------------------
% 1.41/0.57  % (21635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (21635)Termination reason: Satisfiable
% 1.41/0.57  
% 1.41/0.57  % (21635)Memory used [KB]: 10746
% 1.41/0.57  % (21635)Time elapsed: 0.149 s
% 1.41/0.57  % (21635)------------------------------
% 1.41/0.57  % (21635)------------------------------
% 1.41/0.58  % (21613)Success in time 0.204 s
%------------------------------------------------------------------------------
