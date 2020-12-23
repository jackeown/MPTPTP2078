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
% DateTime   : Thu Dec  3 13:22:49 EST 2020

% Result     : CounterSatisfiable 0.37s
% Output     : Saturation 0.37s
% Verified   : 
% Statistics : Number of clauses        :   22 (  22 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    0
%              Number of atoms          :   65 (  65 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u25,negated_conjecture,
    ( v7_struct_0(sK0)
    | k4_yellow_0(sK0) = k3_yellow_0(sK0) )).

cnf(u27,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u34,axiom,
    ( v2_yellow_0(X0)
    | ~ v3_yellow_0(X0)
    | ~ l1_orders_2(X0) )).

cnf(u51,negated_conjecture,
    ( ~ v2_yellow_0(sK0)
    | ~ r1_orders_2(sK0,k4_yellow_0(sK0),X0)
    | k4_yellow_0(sK0) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u33,axiom,
    ( v1_yellow_0(X0)
    | ~ v3_yellow_0(X0)
    | ~ l1_orders_2(X0) )).

cnf(u54,negated_conjecture,
    ( ~ v1_yellow_0(sK0)
    | ~ r1_orders_2(sK0,X1,k3_yellow_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k3_yellow_0(sK0) = X1
    | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) )).

cnf(u29,negated_conjecture,
    ( v3_yellow_0(sK0) )).

cnf(u36,axiom,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0) )).

cnf(u35,axiom,
    ( r1_orders_2(X0,X1,k4_yellow_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0) )).

cnf(u57,negated_conjecture,
    ( ~ r1_orders_2(sK0,k4_yellow_0(sK0),X0)
    | k4_yellow_0(sK0) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u64,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,k3_yellow_0(sK0))
    | k3_yellow_0(sK0) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u43,negated_conjecture,
    ( ~ r1_orders_2(sK0,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | X0 = X1 )).

cnf(u41,negated_conjecture,
    ( m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0)) )).

cnf(u38,axiom,
    ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u31,axiom,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u60,negated_conjecture,
    ( ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k3_yellow_0(sK0) = X0
    | ~ r1_orders_2(sK0,X0,k3_yellow_0(sK0)) )).

cnf(u28,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u37,axiom,
    ( ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | X1 = X2 )).

cnf(u30,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u32,axiom,
    ( ~ l1_orders_2(X0)
    | k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0) )).

cnf(u39,negated_conjecture,
    ( k4_yellow_0(sK0) = k2_yellow_0(sK0,k1_xboole_0) )).

cnf(u26,negated_conjecture,
    ( k4_yellow_0(sK0) != k3_yellow_0(sK0)
    | ~ v7_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:27:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (828440577)
% 0.14/0.36  ipcrm: permission denied for id (828473346)
% 0.14/0.37  ipcrm: permission denied for id (824836100)
% 0.14/0.37  ipcrm: permission denied for id (823459845)
% 0.14/0.37  ipcrm: permission denied for id (828538886)
% 0.14/0.37  ipcrm: permission denied for id (824934408)
% 0.14/0.37  ipcrm: permission denied for id (823525386)
% 0.14/0.38  ipcrm: permission denied for id (824999947)
% 0.21/0.38  ipcrm: permission denied for id (828637196)
% 0.21/0.38  ipcrm: permission denied for id (825065485)
% 0.21/0.38  ipcrm: permission denied for id (825098254)
% 0.21/0.38  ipcrm: permission denied for id (825163792)
% 0.21/0.38  ipcrm: permission denied for id (825229330)
% 0.21/0.39  ipcrm: permission denied for id (825294868)
% 0.21/0.39  ipcrm: permission denied for id (825360405)
% 0.21/0.39  ipcrm: permission denied for id (825393174)
% 0.21/0.39  ipcrm: permission denied for id (825425943)
% 0.21/0.39  ipcrm: permission denied for id (828768280)
% 0.21/0.39  ipcrm: permission denied for id (823689241)
% 0.21/0.39  ipcrm: permission denied for id (828801050)
% 0.21/0.39  ipcrm: permission denied for id (823722011)
% 0.21/0.40  ipcrm: permission denied for id (828833820)
% 0.21/0.40  ipcrm: permission denied for id (825557021)
% 0.21/0.40  ipcrm: permission denied for id (825622559)
% 0.21/0.40  ipcrm: permission denied for id (825655328)
% 0.21/0.40  ipcrm: permission denied for id (825688097)
% 0.21/0.40  ipcrm: permission denied for id (825720866)
% 0.21/0.41  ipcrm: permission denied for id (823820324)
% 0.21/0.41  ipcrm: permission denied for id (828932133)
% 0.21/0.41  ipcrm: permission denied for id (828964902)
% 0.21/0.41  ipcrm: permission denied for id (825851943)
% 0.21/0.41  ipcrm: permission denied for id (825884712)
% 0.21/0.41  ipcrm: permission denied for id (828997673)
% 0.21/0.41  ipcrm: permission denied for id (825950250)
% 0.21/0.42  ipcrm: permission denied for id (826015788)
% 0.21/0.42  ipcrm: permission denied for id (823918637)
% 0.21/0.42  ipcrm: permission denied for id (826048558)
% 0.21/0.42  ipcrm: permission denied for id (826081327)
% 0.21/0.42  ipcrm: permission denied for id (826114096)
% 0.21/0.42  ipcrm: permission denied for id (829063217)
% 0.21/0.42  ipcrm: permission denied for id (824016946)
% 0.21/0.42  ipcrm: permission denied for id (824049715)
% 0.21/0.43  ipcrm: permission denied for id (826212405)
% 0.21/0.43  ipcrm: permission denied for id (826245174)
% 0.21/0.43  ipcrm: permission denied for id (829128759)
% 0.21/0.43  ipcrm: permission denied for id (826310712)
% 0.21/0.43  ipcrm: permission denied for id (829161529)
% 0.21/0.43  ipcrm: permission denied for id (829194298)
% 0.21/0.43  ipcrm: permission denied for id (824082491)
% 0.21/0.43  ipcrm: permission denied for id (826409020)
% 0.21/0.44  ipcrm: permission denied for id (826441789)
% 0.21/0.44  ipcrm: permission denied for id (829227070)
% 0.21/0.44  ipcrm: permission denied for id (829259839)
% 0.21/0.44  ipcrm: permission denied for id (829292608)
% 0.21/0.44  ipcrm: permission denied for id (829423682)
% 0.21/0.44  ipcrm: permission denied for id (826671171)
% 0.21/0.45  ipcrm: permission denied for id (824180805)
% 0.21/0.45  ipcrm: permission denied for id (824213574)
% 0.21/0.45  ipcrm: permission denied for id (826736711)
% 0.21/0.45  ipcrm: permission denied for id (826769480)
% 0.21/0.45  ipcrm: permission denied for id (826867787)
% 0.21/0.45  ipcrm: permission denied for id (829521996)
% 0.21/0.46  ipcrm: permission denied for id (824279119)
% 0.21/0.46  ipcrm: permission denied for id (829620304)
% 0.21/0.46  ipcrm: permission denied for id (824311889)
% 0.21/0.46  ipcrm: permission denied for id (829685843)
% 0.21/0.46  ipcrm: permission denied for id (829718612)
% 0.21/0.46  ipcrm: permission denied for id (827129941)
% 0.21/0.47  ipcrm: permission denied for id (827162710)
% 0.21/0.47  ipcrm: permission denied for id (829751383)
% 0.21/0.47  ipcrm: permission denied for id (827261017)
% 0.21/0.47  ipcrm: permission denied for id (827293786)
% 0.21/0.47  ipcrm: permission denied for id (827359324)
% 0.21/0.47  ipcrm: permission denied for id (824410205)
% 0.21/0.47  ipcrm: permission denied for id (827392094)
% 0.21/0.48  ipcrm: permission denied for id (827424863)
% 0.21/0.48  ipcrm: permission denied for id (824475744)
% 0.21/0.48  ipcrm: permission denied for id (827490402)
% 0.21/0.48  ipcrm: permission denied for id (827555940)
% 0.21/0.48  ipcrm: permission denied for id (827621478)
% 0.21/0.49  ipcrm: permission denied for id (827654247)
% 0.21/0.49  ipcrm: permission denied for id (827687016)
% 0.21/0.49  ipcrm: permission denied for id (827719785)
% 0.21/0.49  ipcrm: permission denied for id (829980779)
% 0.21/0.49  ipcrm: permission denied for id (827818092)
% 0.21/0.50  ipcrm: permission denied for id (830111856)
% 0.21/0.50  ipcrm: permission denied for id (827981937)
% 0.21/0.50  ipcrm: permission denied for id (828014706)
% 0.21/0.50  ipcrm: permission denied for id (828080244)
% 0.21/0.50  ipcrm: permission denied for id (824574069)
% 0.21/0.50  ipcrm: permission denied for id (830210167)
% 0.21/0.51  ipcrm: permission denied for id (828342397)
% 0.21/0.51  ipcrm: permission denied for id (828375166)
% 0.21/0.51  ipcrm: permission denied for id (824672383)
% 0.37/0.65  % (28070)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.37/0.65  % (28081)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.37/0.66  % (28067)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.37/0.66  % (28076)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.37/0.66  % (28072)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.37/0.66  % (28070)Refutation not found, incomplete strategy% (28070)------------------------------
% 0.37/0.66  % (28070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.66  % (28070)Termination reason: Refutation not found, incomplete strategy
% 0.37/0.66  
% 0.37/0.66  % (28070)Memory used [KB]: 6268
% 0.37/0.66  % (28070)Time elapsed: 0.106 s
% 0.37/0.66  % (28070)------------------------------
% 0.37/0.66  % (28070)------------------------------
% 0.37/0.66  % (28081)Refutation not found, incomplete strategy% (28081)------------------------------
% 0.37/0.66  % (28081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.66  % (28081)Termination reason: Refutation not found, incomplete strategy
% 0.37/0.66  
% 0.37/0.66  % (28081)Memory used [KB]: 6140
% 0.37/0.66  % (28081)Time elapsed: 0.003 s
% 0.37/0.66  % (28081)------------------------------
% 0.37/0.66  % (28081)------------------------------
% 0.37/0.66  % (28089)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.37/0.66  % (28076)Refutation not found, incomplete strategy% (28076)------------------------------
% 0.37/0.66  % (28076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.66  % (28076)Termination reason: Refutation not found, incomplete strategy
% 0.37/0.66  
% 0.37/0.66  % (28076)Memory used [KB]: 10618
% 0.37/0.66  % (28076)Time elapsed: 0.113 s
% 0.37/0.66  % (28076)------------------------------
% 0.37/0.66  % (28076)------------------------------
% 0.37/0.66  % (28088)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.37/0.67  % (28089)Refutation not found, incomplete strategy% (28089)------------------------------
% 0.37/0.67  % (28089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.67  % (28089)Termination reason: Refutation not found, incomplete strategy
% 0.37/0.67  
% 0.37/0.67  % (28089)Memory used [KB]: 1791
% 0.37/0.67  % (28089)Time elapsed: 0.112 s
% 0.37/0.67  % (28089)------------------------------
% 0.37/0.67  % (28089)------------------------------
% 0.37/0.67  % (28074)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.37/0.67  % (28068)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.37/0.67  % (28080)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.37/0.67  % (28074)Refutation not found, incomplete strategy% (28074)------------------------------
% 0.37/0.67  % (28074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.67  % (28074)Termination reason: Refutation not found, incomplete strategy
% 0.37/0.67  
% 0.37/0.67  % (28074)Memory used [KB]: 10746
% 0.37/0.67  % (28074)Time elapsed: 0.106 s
% 0.37/0.67  % (28074)------------------------------
% 0.37/0.67  % (28074)------------------------------
% 0.37/0.67  % SZS status CounterSatisfiable for theBenchmark
% 0.37/0.67  % (28072)# SZS output start Saturation.
% 0.37/0.67  cnf(u25,negated_conjecture,
% 0.37/0.67      v7_struct_0(sK0) | k4_yellow_0(sK0) = k3_yellow_0(sK0)).
% 0.37/0.67  
% 0.37/0.67  cnf(u27,negated_conjecture,
% 0.37/0.67      ~v2_struct_0(sK0)).
% 0.37/0.67  
% 0.37/0.67  cnf(u34,axiom,
% 0.37/0.67      v2_yellow_0(X0) | ~v3_yellow_0(X0) | ~l1_orders_2(X0)).
% 0.37/0.67  
% 0.37/0.67  cnf(u51,negated_conjecture,
% 0.37/0.67      ~v2_yellow_0(sK0) | ~r1_orders_2(sK0,k4_yellow_0(sK0),X0) | k4_yellow_0(sK0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 0.37/0.67  
% 0.37/0.67  cnf(u33,axiom,
% 0.37/0.67      v1_yellow_0(X0) | ~v3_yellow_0(X0) | ~l1_orders_2(X0)).
% 0.37/0.67  
% 0.37/0.67  cnf(u54,negated_conjecture,
% 0.37/0.67      ~v1_yellow_0(sK0) | ~r1_orders_2(sK0,X1,k3_yellow_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k3_yellow_0(sK0) = X1 | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))).
% 0.37/0.67  
% 0.37/0.67  cnf(u29,negated_conjecture,
% 0.37/0.67      v3_yellow_0(sK0)).
% 0.37/0.67  
% 0.37/0.67  cnf(u36,axiom,
% 0.37/0.67      r1_orders_2(X0,k3_yellow_0(X0),X1) | ~v5_orders_2(X0) | ~v1_yellow_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)).
% 0.37/0.67  
% 0.37/0.67  cnf(u35,axiom,
% 0.37/0.67      r1_orders_2(X0,X1,k4_yellow_0(X0)) | ~v5_orders_2(X0) | ~v2_yellow_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)).
% 0.37/0.67  
% 0.37/0.67  cnf(u57,negated_conjecture,
% 0.37/0.67      ~r1_orders_2(sK0,k4_yellow_0(sK0),X0) | k4_yellow_0(sK0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 0.37/0.67  
% 0.37/0.67  cnf(u64,negated_conjecture,
% 0.37/0.67      ~r1_orders_2(sK0,X0,k3_yellow_0(sK0)) | k3_yellow_0(sK0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 0.37/0.67  
% 0.37/0.67  cnf(u43,negated_conjecture,
% 0.37/0.67      ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | X0 = X1).
% 0.37/0.67  
% 0.37/0.67  cnf(u41,negated_conjecture,
% 0.37/0.67      m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0))).
% 0.37/0.67  
% 0.37/0.67  cnf(u38,axiom,
% 0.37/0.67      m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.37/0.67  
% 0.37/0.67  cnf(u31,axiom,
% 0.37/0.67      m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.37/0.67  
% 0.37/0.67  cnf(u60,negated_conjecture,
% 0.37/0.67      ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k3_yellow_0(sK0) = X0 | ~r1_orders_2(sK0,X0,k3_yellow_0(sK0))).
% 0.37/0.67  
% 0.37/0.67  cnf(u28,negated_conjecture,
% 0.37/0.67      v5_orders_2(sK0)).
% 0.37/0.67  
% 0.37/0.67  cnf(u37,axiom,
% 0.37/0.67      ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X2,X1) | X1 = X2).
% 0.37/0.67  
% 0.37/0.67  cnf(u30,negated_conjecture,
% 0.37/0.67      l1_orders_2(sK0)).
% 0.37/0.67  
% 0.37/0.67  cnf(u32,axiom,
% 0.37/0.67      ~l1_orders_2(X0) | k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0)).
% 0.37/0.67  
% 0.37/0.67  cnf(u39,negated_conjecture,
% 0.37/0.67      k4_yellow_0(sK0) = k2_yellow_0(sK0,k1_xboole_0)).
% 0.37/0.67  
% 0.37/0.67  cnf(u26,negated_conjecture,
% 0.37/0.67      k4_yellow_0(sK0) != k3_yellow_0(sK0) | ~v7_struct_0(sK0)).
% 0.37/0.67  
% 0.37/0.67  % (28072)# SZS output end Saturation.
% 0.37/0.67  % (28072)------------------------------
% 0.37/0.67  % (28072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.37/0.67  % (28072)Termination reason: Satisfiable
% 0.37/0.67  
% 0.37/0.67  % (28072)Memory used [KB]: 6268
% 0.37/0.67  % (28072)Time elapsed: 0.094 s
% 0.37/0.67  % (28072)------------------------------
% 0.37/0.67  % (28072)------------------------------
% 0.37/0.67  % (27932)Success in time 0.313 s
%------------------------------------------------------------------------------
