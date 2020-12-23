%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:57 EST 2020

% Result     : CounterSatisfiable 1.32s
% Output     : Saturation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   46 (  46 expanded)
%              Number of leaves         :   46 (  46 expanded)
%              Depth                    :    0
%              Number of atoms          :  121 ( 121 expanded)
%              Number of equality atoms :   66 (  66 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u397,axiom,(
    ! [X1,X0] :
      ( X0 != X1
      | sK3(X0,k1_tarski(X1)) = X0
      | k1_tarski(X0) = k1_tarski(X1) ) )).

tff(u396,axiom,(
    ! [X1,X0] :
      ( X0 != X1
      | sK3(X0,k1_tarski(X1)) = X1
      | k1_tarski(X0) = k1_tarski(X1) ) )).

tff(u395,axiom,(
    ! [X1,X0,X2] :
      ( sK3(X2,k1_tarski(X1)) != X0
      | sK3(X0,k1_tarski(X1)) = sK3(X2,k1_tarski(X1))
      | sK3(X2,k1_tarski(X1)) = X2
      | k1_tarski(X0) = k1_tarski(X1)
      | k1_tarski(X1) = k1_tarski(X2) ) )).

tff(u394,axiom,(
    ! [X1,X0,X2] :
      ( sK3(X2,k1_tarski(X1)) != X0
      | sK3(X2,k1_tarski(X1)) = X2
      | sK3(X0,k1_tarski(X1)) = X0
      | k1_tarski(X1) = k1_tarski(X2)
      | k1_tarski(X0) = k1_tarski(X1) ) )).

tff(u393,negated_conjecture,
    ( ~ ( k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1) )
    | k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1) )).

tff(u392,negated_conjecture,
    ( ~ ( k6_domain_1(u1_struct_0(sK0),sK2) != k1_tarski(sK2) )
    | k6_domain_1(u1_struct_0(sK0),sK2) != k1_tarski(sK2) )).

tff(u391,negated_conjecture,
    ( ~ ( k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) != k1_tarski(u1_orders_2(sK0)) )
    | k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) != k1_tarski(u1_orders_2(sK0)) )).

tff(u390,negated_conjecture,
    ( ~ ( k6_waybel_0(sK0,sK1) != k1_tarski(sK2) )
    | k6_waybel_0(sK0,sK1) != k1_tarski(sK2) )).

tff(u389,negated_conjecture,
    ( ~ ( u1_orders_2(sK0) != k1_tarski(k4_tarski(sK1,sK2)) )
    | u1_orders_2(sK0) != k1_tarski(k4_tarski(sK1,sK2)) )).

tff(u388,negated_conjecture,
    ( ~ ( sK2 != sK3(sK2,k6_waybel_0(sK0,sK1)) )
    | sK2 != sK3(sK2,k6_waybel_0(sK0,sK1)) )).

tff(u387,axiom,(
    ! [X1,X0] :
      ( sK3(X0,X1) != sK3(sK3(X0,X1),X1)
      | k1_tarski(X0) = X1
      | sK3(X0,X1) = X0
      | k1_tarski(sK3(X0,X1)) = X1 ) )).

tff(u386,axiom,(
    ! [X5,X4] :
      ( sK3(X4,k1_tarski(X5)) = X4
      | sK3(X4,k1_tarski(X5)) = X5
      | k1_tarski(X5) = k1_tarski(X4) ) )).

tff(u385,axiom,(
    ! [X9,X7,X8] :
      ( sK3(X9,k1_tarski(X8)) = X9
      | sK3(X7,k1_tarski(X8)) = sK3(X9,k1_tarski(X8))
      | sK3(X7,k1_tarski(X8)) = X7
      | k1_tarski(X9) = k1_tarski(X8)
      | k1_tarski(X7) = k1_tarski(X8) ) )).

tff(u384,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ! [X0] :
        ( sK3(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = X0
        | k1_tarski(X0) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ) )).

tff(u383,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X0] :
        ( sK3(X0,u1_struct_0(sK0)) = X0
        | k1_tarski(X0) = u1_struct_0(sK0) ) )).

tff(u382,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X1] :
        ( sK3(X1,u1_orders_2(sK0)) = X1
        | k1_tarski(X1) = u1_orders_2(sK0) ) )).

tff(u381,axiom,(
    ! [X3,X2] :
      ( sK3(sK3(X2,k1_tarski(X3)),k1_tarski(X3)) = X3
      | sK3(X2,k1_tarski(X3)) = X2
      | k1_tarski(X3) = k1_tarski(sK3(X2,k1_tarski(X3)))
      | k1_tarski(X3) = k1_tarski(X2) ) )).

tff(u380,negated_conjecture,
    ( k4_tarski(sK1,sK2) != sK3(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | k4_tarski(sK1,sK2) = sK3(k4_tarski(sK1,sK2),u1_orders_2(sK0)) )).

tff(u379,axiom,(
    ! [X1,X0] :
      ( k1_tarski(X1) = k1_tarski(sK3(X0,k1_tarski(X1)))
      | sK3(X0,k1_tarski(X1)) = X0
      | k1_tarski(X0) = k1_tarski(X1) ) )).

tff(u378,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u377,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X0,X1)
      | sK3(X0,X1) != X0
      | k1_tarski(X0) = X1 ) )).

tff(u376,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) )).

tff(u375,axiom,(
    ! [X3,X2,X4] :
      ( ~ r2_hidden(X4,k1_tarski(X3))
      | sK3(X2,k1_tarski(X3)) = X4
      | sK3(X2,k1_tarski(X3)) = X2
      | k1_tarski(X3) = k1_tarski(X2) ) )).

tff(u374,axiom,(
    ! [X3,X0] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) )).

tff(u373,axiom,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) )).

tff(u372,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK3(X0,X1),X1)
      | sK3(X0,X1) = X0
      | k1_tarski(X0) = X1 ) )).

tff(u371,negated_conjecture,
    ( ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | r2_hidden(sK2,k6_waybel_0(sK0,sK1)) )).

tff(u370,axiom,(
    ! [X3,X2] :
      ( ~ v1_xboole_0(X3)
      | k1_tarski(X2) = X3
      | sK3(X2,X3) = X2 ) )).

tff(u369,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) )).

tff(u368,negated_conjecture,
    ( ~ ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u367,negated_conjecture,
    ( ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | ~ v1_xboole_0(k6_waybel_0(sK0,sK1)) )).

tff(u366,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) )).

tff(u365,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_orders_2(sK0)) )).

tff(u364,negated_conjecture,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u363,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) )).

tff(u362,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) )).

tff(u361,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) )).

tff(u360,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) )).

tff(u359,negated_conjecture,
    ( ~ ~ m1_subset_1(k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))
    | ~ m1_subset_1(k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) )).

tff(u358,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u357,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u356,negated_conjecture,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u355,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) )).

tff(u354,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u353,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u352,negated_conjecture,
    ( ~ ~ r1_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK1,sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:16:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (8418)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (8411)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (8424)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (8410)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (8423)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (8411)Refutation not found, incomplete strategy% (8411)------------------------------
% 0.22/0.51  % (8411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8406)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (8408)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (8407)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (8427)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (8411)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (8411)Memory used [KB]: 10490
% 0.22/0.51  % (8411)Time elapsed: 0.094 s
% 0.22/0.51  % (8411)------------------------------
% 0.22/0.51  % (8411)------------------------------
% 0.22/0.51  % (8418)Refutation not found, incomplete strategy% (8418)------------------------------
% 0.22/0.51  % (8418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (8418)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (8418)Memory used [KB]: 6140
% 0.22/0.52  % (8418)Time elapsed: 0.104 s
% 0.22/0.52  % (8418)------------------------------
% 0.22/0.52  % (8418)------------------------------
% 0.22/0.52  % (8426)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (8419)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (8428)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (8415)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (8416)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (8416)Refutation not found, incomplete strategy% (8416)------------------------------
% 0.22/0.53  % (8416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8416)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (8416)Memory used [KB]: 10490
% 0.22/0.53  % (8416)Time elapsed: 0.116 s
% 0.22/0.53  % (8416)------------------------------
% 0.22/0.53  % (8416)------------------------------
% 0.22/0.53  % (8412)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (8412)Refutation not found, incomplete strategy% (8412)------------------------------
% 0.22/0.53  % (8412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8412)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (8412)Memory used [KB]: 1663
% 0.22/0.53  % (8412)Time elapsed: 0.083 s
% 0.22/0.53  % (8412)------------------------------
% 0.22/0.53  % (8412)------------------------------
% 1.32/0.53  % (8405)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.32/0.54  % (8414)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.32/0.54  % (8405)Refutation not found, incomplete strategy% (8405)------------------------------
% 1.32/0.54  % (8405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (8405)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (8405)Memory used [KB]: 10490
% 1.32/0.54  % (8405)Time elapsed: 0.110 s
% 1.32/0.54  % (8405)------------------------------
% 1.32/0.54  % (8405)------------------------------
% 1.32/0.54  % (8420)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.32/0.54  % (8422)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.32/0.54  % (8406)Refutation not found, incomplete strategy% (8406)------------------------------
% 1.32/0.54  % (8406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (8406)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (8406)Memory used [KB]: 10618
% 1.32/0.54  % (8406)Time elapsed: 0.122 s
% 1.32/0.54  % (8406)------------------------------
% 1.32/0.54  % (8406)------------------------------
% 1.32/0.55  % (8430)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.32/0.55  % (8429)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.32/0.55  % SZS status CounterSatisfiable for theBenchmark
% 1.32/0.55  % (8415)# SZS output start Saturation.
% 1.32/0.55  tff(u397,axiom,
% 1.32/0.55      (![X1, X0] : (((X0 != X1) | (sK3(X0,k1_tarski(X1)) = X0) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 1.32/0.55  
% 1.32/0.55  tff(u396,axiom,
% 1.32/0.55      (![X1, X0] : (((X0 != X1) | (sK3(X0,k1_tarski(X1)) = X1) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 1.32/0.55  
% 1.32/0.55  tff(u395,axiom,
% 1.32/0.55      (![X1, X0, X2] : (((sK3(X2,k1_tarski(X1)) != X0) | (sK3(X0,k1_tarski(X1)) = sK3(X2,k1_tarski(X1))) | (sK3(X2,k1_tarski(X1)) = X2) | (k1_tarski(X0) = k1_tarski(X1)) | (k1_tarski(X1) = k1_tarski(X2)))))).
% 1.32/0.55  
% 1.32/0.55  tff(u394,axiom,
% 1.32/0.55      (![X1, X0, X2] : (((sK3(X2,k1_tarski(X1)) != X0) | (sK3(X2,k1_tarski(X1)) = X2) | (sK3(X0,k1_tarski(X1)) = X0) | (k1_tarski(X1) = k1_tarski(X2)) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 1.32/0.55  
% 1.32/0.55  tff(u393,negated_conjecture,
% 1.32/0.55      ((~(k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1)))).
% 1.32/0.55  
% 1.32/0.55  tff(u392,negated_conjecture,
% 1.32/0.55      ((~(k6_domain_1(u1_struct_0(sK0),sK2) != k1_tarski(sK2))) | (k6_domain_1(u1_struct_0(sK0),sK2) != k1_tarski(sK2)))).
% 1.32/0.55  
% 1.32/0.55  tff(u391,negated_conjecture,
% 1.32/0.55      ((~(k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) != k1_tarski(u1_orders_2(sK0)))) | (k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) != k1_tarski(u1_orders_2(sK0))))).
% 1.32/0.55  
% 1.32/0.55  tff(u390,negated_conjecture,
% 1.32/0.55      ((~(k6_waybel_0(sK0,sK1) != k1_tarski(sK2))) | (k6_waybel_0(sK0,sK1) != k1_tarski(sK2)))).
% 1.32/0.55  
% 1.32/0.55  tff(u389,negated_conjecture,
% 1.32/0.55      ((~(u1_orders_2(sK0) != k1_tarski(k4_tarski(sK1,sK2)))) | (u1_orders_2(sK0) != k1_tarski(k4_tarski(sK1,sK2))))).
% 1.32/0.55  
% 1.32/0.55  tff(u388,negated_conjecture,
% 1.32/0.55      ((~(sK2 != sK3(sK2,k6_waybel_0(sK0,sK1)))) | (sK2 != sK3(sK2,k6_waybel_0(sK0,sK1))))).
% 1.32/0.55  
% 1.32/0.55  tff(u387,axiom,
% 1.32/0.55      (![X1, X0] : (((sK3(X0,X1) != sK3(sK3(X0,X1),X1)) | (k1_tarski(X0) = X1) | (sK3(X0,X1) = X0) | (k1_tarski(sK3(X0,X1)) = X1))))).
% 1.32/0.55  
% 1.32/0.55  tff(u386,axiom,
% 1.32/0.55      (![X5, X4] : (((sK3(X4,k1_tarski(X5)) = X4) | (sK3(X4,k1_tarski(X5)) = X5) | (k1_tarski(X5) = k1_tarski(X4)))))).
% 1.32/0.55  
% 1.32/0.55  tff(u385,axiom,
% 1.32/0.55      (![X9, X7, X8] : (((sK3(X9,k1_tarski(X8)) = X9) | (sK3(X7,k1_tarski(X8)) = sK3(X9,k1_tarski(X8))) | (sK3(X7,k1_tarski(X8)) = X7) | (k1_tarski(X9) = k1_tarski(X8)) | (k1_tarski(X7) = k1_tarski(X8)))))).
% 1.32/0.55  
% 1.32/0.55  tff(u384,negated_conjecture,
% 1.32/0.55      ((~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | (![X0] : (((sK3(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = X0) | (k1_tarski(X0) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))))))).
% 1.32/0.55  
% 1.32/0.55  tff(u383,negated_conjecture,
% 1.32/0.55      ((~v1_xboole_0(u1_struct_0(sK0))) | (![X0] : (((sK3(X0,u1_struct_0(sK0)) = X0) | (k1_tarski(X0) = u1_struct_0(sK0))))))).
% 1.32/0.55  
% 1.32/0.55  tff(u382,negated_conjecture,
% 1.32/0.55      ((~v1_xboole_0(u1_struct_0(sK0))) | (![X1] : (((sK3(X1,u1_orders_2(sK0)) = X1) | (k1_tarski(X1) = u1_orders_2(sK0))))))).
% 1.32/0.55  
% 1.32/0.55  tff(u381,axiom,
% 1.32/0.55      (![X3, X2] : (((sK3(sK3(X2,k1_tarski(X3)),k1_tarski(X3)) = X3) | (sK3(X2,k1_tarski(X3)) = X2) | (k1_tarski(X3) = k1_tarski(sK3(X2,k1_tarski(X3)))) | (k1_tarski(X3) = k1_tarski(X2)))))).
% 1.32/0.55  
% 1.32/0.55  tff(u380,negated_conjecture,
% 1.32/0.55      ((~(k4_tarski(sK1,sK2) = sK3(k4_tarski(sK1,sK2),u1_orders_2(sK0)))) | (k4_tarski(sK1,sK2) = sK3(k4_tarski(sK1,sK2),u1_orders_2(sK0))))).
% 1.32/0.55  
% 1.32/0.55  tff(u379,axiom,
% 1.32/0.55      (![X1, X0] : (((k1_tarski(X1) = k1_tarski(sK3(X0,k1_tarski(X1)))) | (sK3(X0,k1_tarski(X1)) = X0) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 1.32/0.55  
% 1.32/0.55  tff(u378,axiom,
% 1.32/0.55      (![X1, X0, X2] : ((~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.32/0.55  
% 1.32/0.55  tff(u377,axiom,
% 1.32/0.55      (![X1, X0] : ((~r2_hidden(X0,X1) | (sK3(X0,X1) != X0) | (k1_tarski(X0) = X1))))).
% 1.32/0.55  
% 1.32/0.55  tff(u376,axiom,
% 1.32/0.55      (![X1, X0] : ((~r2_hidden(X0,X1) | ~v1_xboole_0(X1))))).
% 1.32/0.55  
% 1.32/0.55  tff(u375,axiom,
% 1.32/0.55      (![X3, X2, X4] : ((~r2_hidden(X4,k1_tarski(X3)) | (sK3(X2,k1_tarski(X3)) = X4) | (sK3(X2,k1_tarski(X3)) = X2) | (k1_tarski(X3) = k1_tarski(X2)))))).
% 1.32/0.55  
% 1.32/0.55  tff(u374,axiom,
% 1.32/0.55      (![X3, X0] : ((~r2_hidden(X3,k1_tarski(X0)) | (X0 = X3))))).
% 1.32/0.55  
% 1.32/0.55  tff(u373,axiom,
% 1.32/0.55      (![X3] : (r2_hidden(X3,k1_tarski(X3))))).
% 1.32/0.55  
% 1.32/0.55  tff(u372,axiom,
% 1.32/0.55      (![X1, X0] : ((r2_hidden(sK3(X0,X1),X1) | (sK3(X0,X1) = X0) | (k1_tarski(X0) = X1))))).
% 1.32/0.55  
% 1.32/0.55  tff(u371,negated_conjecture,
% 1.32/0.55      ((~r2_hidden(sK2,k6_waybel_0(sK0,sK1))) | r2_hidden(sK2,k6_waybel_0(sK0,sK1)))).
% 1.32/0.55  
% 1.32/0.55  tff(u370,axiom,
% 1.32/0.55      (![X3, X2] : ((~v1_xboole_0(X3) | (k1_tarski(X2) = X3) | (sK3(X2,X3) = X2))))).
% 1.32/0.55  
% 1.32/0.55  tff(u369,axiom,
% 1.32/0.55      (![X0] : (~v1_xboole_0(k1_tarski(X0))))).
% 1.32/0.55  
% 1.32/0.55  tff(u368,negated_conjecture,
% 1.32/0.55      ((~~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 1.32/0.55  
% 1.32/0.55  tff(u367,negated_conjecture,
% 1.32/0.55      ((~r2_hidden(sK2,k6_waybel_0(sK0,sK1))) | ~v1_xboole_0(k6_waybel_0(sK0,sK1)))).
% 1.32/0.55  
% 1.32/0.55  tff(u366,negated_conjecture,
% 1.32/0.55      ((~v1_xboole_0(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)))).
% 1.32/0.55  
% 1.32/0.55  tff(u365,negated_conjecture,
% 1.32/0.55      ((~v1_xboole_0(u1_struct_0(sK0))) | v1_xboole_0(u1_orders_2(sK0)))).
% 1.32/0.55  
% 1.32/0.55  tff(u364,negated_conjecture,
% 1.32/0.55      ((~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))).
% 1.32/0.55  
% 1.32/0.55  tff(u363,axiom,
% 1.32/0.55      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1))))).
% 1.32/0.55  
% 1.32/0.55  tff(u362,axiom,
% 1.32/0.55      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_xboole_0(X0))))).
% 1.32/0.55  
% 1.32/0.55  tff(u361,axiom,
% 1.32/0.55      (![X1, X0] : ((~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | v1_xboole_0(X0))))).
% 1.32/0.55  
% 1.32/0.55  tff(u360,axiom,
% 1.32/0.55      (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k1_tarski(X1)) | v1_xboole_0(X0))))).
% 1.32/0.55  
% 1.32/0.55  tff(u359,negated_conjecture,
% 1.32/0.55      ((~~m1_subset_1(k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))) | ~m1_subset_1(k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))))).
% 1.32/0.55  
% 1.32/0.55  tff(u358,negated_conjecture,
% 1.32/0.55      m1_subset_1(sK1,u1_struct_0(sK0))).
% 1.32/0.55  
% 1.32/0.55  tff(u357,negated_conjecture,
% 1.32/0.55      m1_subset_1(sK2,u1_struct_0(sK0))).
% 1.32/0.55  
% 1.32/0.55  tff(u356,negated_conjecture,
% 1.32/0.55      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 1.32/0.55  
% 1.32/0.55  tff(u355,axiom,
% 1.32/0.55      (![X0] : ((~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))))).
% 1.32/0.55  
% 1.32/0.55  tff(u354,negated_conjecture,
% 1.32/0.55      l1_orders_2(sK0)).
% 1.32/0.55  
% 1.32/0.55  tff(u353,axiom,
% 1.32/0.55      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,X2) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.32/0.55  
% 1.32/0.55  tff(u352,negated_conjecture,
% 1.32/0.55      ((~~r1_orders_2(sK0,sK1,sK2)) | ~r1_orders_2(sK0,sK1,sK2))).
% 1.32/0.55  
% 1.32/0.55  % (8415)# SZS output end Saturation.
% 1.32/0.55  % (8415)------------------------------
% 1.32/0.55  % (8415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (8415)Termination reason: Satisfiable
% 1.32/0.55  
% 1.32/0.55  % (8415)Memory used [KB]: 10746
% 1.32/0.55  % (8415)Time elapsed: 0.121 s
% 1.32/0.55  % (8415)------------------------------
% 1.32/0.55  % (8415)------------------------------
% 1.32/0.55  % (8404)Success in time 0.183 s
%------------------------------------------------------------------------------
