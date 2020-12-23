%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:57 EST 2020

% Result     : CounterSatisfiable 1.62s
% Output     : Saturation 1.62s
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
    ( ~ ( k5_waybel_0(sK0,sK1) != k1_tarski(sK2) )
    | k5_waybel_0(sK0,sK1) != k1_tarski(sK2) )).

tff(u389,negated_conjecture,
    ( ~ ( u1_orders_2(sK0) != k1_tarski(k4_tarski(sK2,sK1)) )
    | u1_orders_2(sK0) != k1_tarski(k4_tarski(sK2,sK1)) )).

tff(u388,negated_conjecture,
    ( ~ ( sK2 != sK3(sK2,k5_waybel_0(sK0,sK1)) )
    | sK2 != sK3(sK2,k5_waybel_0(sK0,sK1)) )).

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
    ( k4_tarski(sK2,sK1) != sK3(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | k4_tarski(sK2,sK1) = sK3(k4_tarski(sK2,sK1),u1_orders_2(sK0)) )).

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
    ( ~ r2_hidden(sK2,k5_waybel_0(sK0,sK1))
    | r2_hidden(sK2,k5_waybel_0(sK0,sK1)) )).

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
    ( ~ r2_hidden(sK2,k5_waybel_0(sK0,sK1))
    | ~ v1_xboole_0(k5_waybel_0(sK0,sK1)) )).

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
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
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
    ( ~ ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK2,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (28273)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.49  % (28274)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (28274)Refutation not found, incomplete strategy% (28274)------------------------------
% 0.20/0.50  % (28274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (28274)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (28274)Memory used [KB]: 10490
% 0.20/0.50  % (28274)Time elapsed: 0.075 s
% 0.20/0.50  % (28274)------------------------------
% 0.20/0.50  % (28274)------------------------------
% 0.20/0.50  % (28289)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (28290)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (28281)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (28268)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.52  % (28270)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.52  % (28272)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.52  % (28287)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (28283)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (28268)Refutation not found, incomplete strategy% (28268)------------------------------
% 0.20/0.52  % (28268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (28268)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (28268)Memory used [KB]: 10490
% 0.20/0.52  % (28268)Time elapsed: 0.096 s
% 0.20/0.52  % (28268)------------------------------
% 0.20/0.52  % (28268)------------------------------
% 0.20/0.53  % (28280)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.53  % (28280)Refutation not found, incomplete strategy% (28280)------------------------------
% 0.20/0.53  % (28280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28280)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (28280)Memory used [KB]: 10490
% 0.20/0.53  % (28280)Time elapsed: 0.121 s
% 0.20/0.53  % (28280)------------------------------
% 0.20/0.53  % (28280)------------------------------
% 0.20/0.53  % (28294)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.53  % (28288)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.53  % (28269)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (28269)Refutation not found, incomplete strategy% (28269)------------------------------
% 0.20/0.53  % (28269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (28269)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (28269)Memory used [KB]: 10618
% 0.20/0.53  % (28269)Time elapsed: 0.129 s
% 0.20/0.53  % (28269)------------------------------
% 0.20/0.53  % (28269)------------------------------
% 0.20/0.54  % (28285)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.43/0.54  % (28276)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.43/0.54  % (28276)Refutation not found, incomplete strategy% (28276)------------------------------
% 1.43/0.54  % (28276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (28276)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.54  
% 1.43/0.54  % (28276)Memory used [KB]: 1663
% 1.43/0.54  % (28276)Time elapsed: 0.097 s
% 1.43/0.54  % (28276)------------------------------
% 1.43/0.54  % (28276)------------------------------
% 1.43/0.54  % (28279)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.43/0.54  % (28278)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.43/0.54  % (28282)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.43/0.54  % (28282)Refutation not found, incomplete strategy% (28282)------------------------------
% 1.43/0.54  % (28282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.54  % (28282)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.54  
% 1.43/0.54  % (28282)Memory used [KB]: 6140
% 1.43/0.54  % (28282)Time elapsed: 0.128 s
% 1.43/0.54  % (28282)------------------------------
% 1.43/0.54  % (28282)------------------------------
% 1.43/0.54  % (28292)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.43/0.54  % (28271)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.43/0.55  % (28284)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.43/0.55  % (28277)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.43/0.55  % (28291)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.43/0.56  % (28286)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.62/0.56  % (28293)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.62/0.56  % SZS status CounterSatisfiable for theBenchmark
% 1.62/0.56  % (28279)# SZS output start Saturation.
% 1.62/0.56  tff(u397,axiom,
% 1.62/0.56      (![X1, X0] : (((X0 != X1) | (sK3(X0,k1_tarski(X1)) = X0) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 1.62/0.56  
% 1.62/0.56  tff(u396,axiom,
% 1.62/0.56      (![X1, X0] : (((X0 != X1) | (sK3(X0,k1_tarski(X1)) = X1) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 1.62/0.56  
% 1.62/0.56  tff(u395,axiom,
% 1.62/0.56      (![X1, X0, X2] : (((sK3(X2,k1_tarski(X1)) != X0) | (sK3(X0,k1_tarski(X1)) = sK3(X2,k1_tarski(X1))) | (sK3(X2,k1_tarski(X1)) = X2) | (k1_tarski(X0) = k1_tarski(X1)) | (k1_tarski(X1) = k1_tarski(X2)))))).
% 1.62/0.56  
% 1.62/0.56  tff(u394,axiom,
% 1.62/0.56      (![X1, X0, X2] : (((sK3(X2,k1_tarski(X1)) != X0) | (sK3(X2,k1_tarski(X1)) = X2) | (sK3(X0,k1_tarski(X1)) = X0) | (k1_tarski(X1) = k1_tarski(X2)) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 1.62/0.56  
% 1.62/0.56  tff(u393,negated_conjecture,
% 1.62/0.56      ((~(k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1)))).
% 1.62/0.56  
% 1.62/0.56  tff(u392,negated_conjecture,
% 1.62/0.56      ((~(k6_domain_1(u1_struct_0(sK0),sK2) != k1_tarski(sK2))) | (k6_domain_1(u1_struct_0(sK0),sK2) != k1_tarski(sK2)))).
% 1.62/0.56  
% 1.62/0.56  tff(u391,negated_conjecture,
% 1.62/0.56      ((~(k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) != k1_tarski(u1_orders_2(sK0)))) | (k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) != k1_tarski(u1_orders_2(sK0))))).
% 1.62/0.56  
% 1.62/0.56  tff(u390,negated_conjecture,
% 1.62/0.56      ((~(k5_waybel_0(sK0,sK1) != k1_tarski(sK2))) | (k5_waybel_0(sK0,sK1) != k1_tarski(sK2)))).
% 1.62/0.56  
% 1.62/0.56  tff(u389,negated_conjecture,
% 1.62/0.56      ((~(u1_orders_2(sK0) != k1_tarski(k4_tarski(sK2,sK1)))) | (u1_orders_2(sK0) != k1_tarski(k4_tarski(sK2,sK1))))).
% 1.62/0.56  
% 1.62/0.56  tff(u388,negated_conjecture,
% 1.62/0.56      ((~(sK2 != sK3(sK2,k5_waybel_0(sK0,sK1)))) | (sK2 != sK3(sK2,k5_waybel_0(sK0,sK1))))).
% 1.62/0.56  
% 1.62/0.56  tff(u387,axiom,
% 1.62/0.56      (![X1, X0] : (((sK3(X0,X1) != sK3(sK3(X0,X1),X1)) | (k1_tarski(X0) = X1) | (sK3(X0,X1) = X0) | (k1_tarski(sK3(X0,X1)) = X1))))).
% 1.62/0.56  
% 1.62/0.56  tff(u386,axiom,
% 1.62/0.56      (![X5, X4] : (((sK3(X4,k1_tarski(X5)) = X4) | (sK3(X4,k1_tarski(X5)) = X5) | (k1_tarski(X5) = k1_tarski(X4)))))).
% 1.62/0.56  
% 1.62/0.56  tff(u385,axiom,
% 1.62/0.56      (![X9, X7, X8] : (((sK3(X9,k1_tarski(X8)) = X9) | (sK3(X7,k1_tarski(X8)) = sK3(X9,k1_tarski(X8))) | (sK3(X7,k1_tarski(X8)) = X7) | (k1_tarski(X9) = k1_tarski(X8)) | (k1_tarski(X7) = k1_tarski(X8)))))).
% 1.62/0.56  
% 1.62/0.56  tff(u384,negated_conjecture,
% 1.62/0.56      ((~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | (![X0] : (((sK3(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = X0) | (k1_tarski(X0) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))))))).
% 1.62/0.56  
% 1.62/0.56  tff(u383,negated_conjecture,
% 1.62/0.56      ((~v1_xboole_0(u1_struct_0(sK0))) | (![X0] : (((sK3(X0,u1_struct_0(sK0)) = X0) | (k1_tarski(X0) = u1_struct_0(sK0))))))).
% 1.62/0.56  
% 1.62/0.56  tff(u382,negated_conjecture,
% 1.62/0.56      ((~v1_xboole_0(u1_struct_0(sK0))) | (![X1] : (((sK3(X1,u1_orders_2(sK0)) = X1) | (k1_tarski(X1) = u1_orders_2(sK0))))))).
% 1.62/0.56  
% 1.62/0.56  tff(u381,axiom,
% 1.62/0.56      (![X3, X2] : (((sK3(sK3(X2,k1_tarski(X3)),k1_tarski(X3)) = X3) | (sK3(X2,k1_tarski(X3)) = X2) | (k1_tarski(X3) = k1_tarski(sK3(X2,k1_tarski(X3)))) | (k1_tarski(X3) = k1_tarski(X2)))))).
% 1.62/0.56  
% 1.62/0.56  tff(u380,negated_conjecture,
% 1.62/0.56      ((~(k4_tarski(sK2,sK1) = sK3(k4_tarski(sK2,sK1),u1_orders_2(sK0)))) | (k4_tarski(sK2,sK1) = sK3(k4_tarski(sK2,sK1),u1_orders_2(sK0))))).
% 1.62/0.56  
% 1.62/0.56  tff(u379,axiom,
% 1.62/0.56      (![X1, X0] : (((k1_tarski(X1) = k1_tarski(sK3(X0,k1_tarski(X1)))) | (sK3(X0,k1_tarski(X1)) = X0) | (k1_tarski(X0) = k1_tarski(X1)))))).
% 1.62/0.56  
% 1.62/0.56  tff(u378,axiom,
% 1.62/0.56      (![X1, X0, X2] : ((~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.62/0.56  
% 1.62/0.56  tff(u377,axiom,
% 1.62/0.56      (![X1, X0] : ((~r2_hidden(X0,X1) | (sK3(X0,X1) != X0) | (k1_tarski(X0) = X1))))).
% 1.62/0.56  
% 1.62/0.56  tff(u376,axiom,
% 1.62/0.56      (![X1, X0] : ((~r2_hidden(X0,X1) | ~v1_xboole_0(X1))))).
% 1.62/0.56  
% 1.62/0.56  tff(u375,axiom,
% 1.62/0.56      (![X3, X2, X4] : ((~r2_hidden(X4,k1_tarski(X3)) | (sK3(X2,k1_tarski(X3)) = X4) | (sK3(X2,k1_tarski(X3)) = X2) | (k1_tarski(X3) = k1_tarski(X2)))))).
% 1.62/0.56  
% 1.62/0.56  tff(u374,axiom,
% 1.62/0.56      (![X3, X0] : ((~r2_hidden(X3,k1_tarski(X0)) | (X0 = X3))))).
% 1.62/0.56  
% 1.62/0.56  tff(u373,axiom,
% 1.62/0.56      (![X3] : (r2_hidden(X3,k1_tarski(X3))))).
% 1.62/0.56  
% 1.62/0.56  tff(u372,axiom,
% 1.62/0.56      (![X1, X0] : ((r2_hidden(sK3(X0,X1),X1) | (sK3(X0,X1) = X0) | (k1_tarski(X0) = X1))))).
% 1.62/0.56  
% 1.62/0.56  tff(u371,negated_conjecture,
% 1.62/0.56      ((~r2_hidden(sK2,k5_waybel_0(sK0,sK1))) | r2_hidden(sK2,k5_waybel_0(sK0,sK1)))).
% 1.62/0.56  
% 1.62/0.56  tff(u370,axiom,
% 1.62/0.56      (![X3, X2] : ((~v1_xboole_0(X3) | (k1_tarski(X2) = X3) | (sK3(X2,X3) = X2))))).
% 1.62/0.56  
% 1.62/0.56  tff(u369,axiom,
% 1.62/0.56      (![X0] : (~v1_xboole_0(k1_tarski(X0))))).
% 1.62/0.56  
% 1.62/0.56  tff(u368,negated_conjecture,
% 1.62/0.56      ((~~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 1.62/0.56  
% 1.62/0.56  tff(u367,negated_conjecture,
% 1.62/0.56      ((~r2_hidden(sK2,k5_waybel_0(sK0,sK1))) | ~v1_xboole_0(k5_waybel_0(sK0,sK1)))).
% 1.62/0.56  
% 1.62/0.56  tff(u366,negated_conjecture,
% 1.62/0.56      ((~v1_xboole_0(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)))).
% 1.62/0.56  
% 1.62/0.56  tff(u365,negated_conjecture,
% 1.62/0.56      ((~v1_xboole_0(u1_struct_0(sK0))) | v1_xboole_0(u1_orders_2(sK0)))).
% 1.62/0.56  
% 1.62/0.56  tff(u364,negated_conjecture,
% 1.62/0.56      ((~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))).
% 1.62/0.56  
% 1.62/0.56  tff(u363,axiom,
% 1.62/0.56      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1))))).
% 1.62/0.56  
% 1.62/0.56  tff(u362,axiom,
% 1.62/0.56      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0))))).
% 1.62/0.56  
% 1.62/0.56  tff(u361,axiom,
% 1.62/0.56      (![X1, X0] : ((~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | v1_xboole_0(X0))))).
% 1.62/0.56  
% 1.62/0.56  tff(u360,axiom,
% 1.62/0.56      (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k1_tarski(X1)) | v1_xboole_0(X0))))).
% 1.62/0.56  
% 1.62/0.56  tff(u359,negated_conjecture,
% 1.62/0.56      ((~~m1_subset_1(k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))) | ~m1_subset_1(k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)),k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))))).
% 1.62/0.56  
% 1.62/0.56  tff(u358,negated_conjecture,
% 1.62/0.56      m1_subset_1(sK1,u1_struct_0(sK0))).
% 1.62/0.56  
% 1.62/0.56  tff(u357,negated_conjecture,
% 1.62/0.56      m1_subset_1(sK2,u1_struct_0(sK0))).
% 1.62/0.56  
% 1.62/0.56  tff(u356,negated_conjecture,
% 1.62/0.56      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 1.62/0.56  
% 1.62/0.56  tff(u355,axiom,
% 1.62/0.56      (![X0] : ((~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))))).
% 1.62/0.56  
% 1.62/0.56  tff(u354,negated_conjecture,
% 1.62/0.56      l1_orders_2(sK0)).
% 1.62/0.56  
% 1.62/0.56  tff(u353,axiom,
% 1.62/0.56      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,X2) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.62/0.56  
% 1.62/0.56  tff(u352,negated_conjecture,
% 1.62/0.56      ((~~r1_orders_2(sK0,sK2,sK1)) | ~r1_orders_2(sK0,sK2,sK1))).
% 1.62/0.56  
% 1.62/0.56  % (28279)# SZS output end Saturation.
% 1.62/0.56  % (28279)------------------------------
% 1.62/0.56  % (28279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.56  % (28279)Termination reason: Satisfiable
% 1.62/0.56  
% 1.62/0.56  % (28279)Memory used [KB]: 10746
% 1.62/0.56  % (28279)Time elapsed: 0.124 s
% 1.62/0.56  % (28279)------------------------------
% 1.62/0.56  % (28279)------------------------------
% 1.62/0.56  % (28261)Success in time 0.209 s
%------------------------------------------------------------------------------
